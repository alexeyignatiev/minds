#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## cover.py
##
##  Created on: Dec 5, 2017
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
import collections
import math
import os
from pysat.card import *
from pysat.examples.lbx import LBX
from pysat.examples.rc2 import RC2, RC2Stratified
from pysat.formula import WCNFPlus
import resource
import socket
import six
from six.moves import range
import sys

# checking whether cplex is available
cplex_present = True
try:
    import cplex
except ImportError:
    cplex_present = False

# checking whether gurobi is available
gurobi_present = True
try:
    import gurobipy as gurobi
except ImportError:
    gurobi_present = False


#
#==============================================================================
class Coverer(object):
    """
        IHS MaxSAT-based rule cover computation.
    """

    def __init__(self, data, clusters, rules, target, options):
        """
            Constructor.
        """

        self.init_stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime
        self.init_ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime

        self.data = data
        self.samps = []
        self.options = options

        self.target = target
        self.cluster = clusters[self.target]
        for i, s in enumerate(self.data.samps):
            self.samps.append(set(s[:-1]))  # needed for the set cover

        # casting rules to sets
        self.rules = [set(r.flits) for r in rules]

    def compute(self):
        """
            Cover samples for all labels (separately).
        """

        self.cover, self.cost = {}, 0

        if self.options.verb:
            print('c2 computing smallest rule cover')

        if self.options.cover == 'mxsat':
            self.compute_mxsat()
        elif self.options.cover == 'cplex':
            self.compute_cplex()
        elif self.options.cover in ('gurobi', 'grb'):
            self.compute_gurobi()

        # recording time
        self.stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_stime
        self.ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - self.init_ctime
        self.time = self.stime + self.ctime

        return self.cover

    def compute_mxsat(self):
        """
            Cover samples for all labels using MaxSAT or MCS enumeration.
        """

        if self.options.verb:
            print('c2 (using rc2)')

        # we model a set cover problem with MaxSAT
        formula = WCNFPlus()

        # hard part of the formula
        if self.options.accuracy == 100.0:
            for sid in self.cluster:  # for every sample in the cluster
                to_hit = []

                for rid, rule in enumerate(self.rules):
                    if rule.issubset(self.samps[sid]):
                        to_hit.append(rid + 1)

                formula.append(to_hit)
        else:
            topv = len(self.rules)
            allvars = []

            # hard clauses first
            for sid in self.cluster:  # for every sample in cluster
                to_hit = []

                for rid, rule in enumerate(self.rules):
                    if rule.issubset(self.samps[sid]):
                        to_hit.append(rid + 1)

                topv += 1
                allvars.append(topv)
                formula.append([-topv] + to_hit)
                for rid in to_hit:
                    formula.append([topv, -rid])

            # forcing at least the given percentage of samples to be covered
            cnum = int(math.ceil(self.options.accuracy * len(allvars) / 100.0))
            al = CardEnc.atleast(allvars, bound=cnum, top_id=topv, encoding=self.options.enc)
            if al:
                for cl in al.clauses:
                    formula.append(cl)

        # soft clauses
        for rid in range(len(self.rules)):
            formula.append([-rid - 1], weight=1)

        if self.options.weighted and not self.options.approx:
            # it is safe to add weights for all rules
            # because each rule covers at least one sample

            formula.wght = [len(rule) + 1 for rule in self.rules]

        if self.options.pdump:
            fname = 'cover{0}.{1}@{2}.wcnf'.format(self.target, os.getpid(), socket.gethostname())
            formula.to_file(fname)

        # choosing the right solver
        if not self.options.approx:
            MaxSAT = RC2Stratified if self.options.blo else RC2
            hitman = MaxSAT(formula, solver=self.options.solver,
                    adapt=self.options.am1, exhaust=self.options.exhaust,
                    trim=self.options.trim, minz=self.options.minz)
        else:
            hitman = LBX(formula, use_cld=self.options.use_cld,
                    solver_name=self.options.solver, use_timer=False)

        # and the cover is...
        if not self.options.approx:
            self.cover = list(filter(lambda l: 0 < l <= len(self.rules) + 1, hitman.compute()))
            self.cost += hitman.cost

            if self.options.weighted:
                self.cost -= len(self.cover)
        else:
            # approximating by computing a number of MCSes
            covers = []
            for i, cover in enumerate(hitman.enumerate()):
                hitman.block(cover)
                if self.options.weighted:
                    cost = sum([len(self.rules[rid - 1]) for rid in cover])
                else:
                    cost = len(cover)

                covers.append([cover, cost])

                if i + 1 == self.options.approx:
                    break

            self.cover, cost = min(covers, key=lambda x: x[1])
            self.cost += cost

        hitman.delete()

    def compute_cplex(self):
        """
            Cover samples for all labels using CPLEX.
        """

        assert cplex_present, 'CPLEX is unavailable'

        if self.options.verb:
            print('c2 (using cplex)')

        # initializing the solver
        hitman = cplex.Cplex()

        # turning logger off
        hitman.set_log_stream(None)
        hitman.set_error_stream(None)
        hitman.set_results_stream(None)
        hitman.set_warning_stream(None)

        # variables
        vnames = ['p_{0}'.format(i + 1) for i in range(len(self.rules))]
        prvars = hitman.variables.add(names=vnames, types='B' * len(vnames))

        # hard constraints
        for sid in self.cluster:  # for every sample in cluster
            to_hit = []

            for rid, rule in enumerate(self.rules):
                if rule.issubset(self.samps[sid]):
                    to_hit.append(vnames[rid])

            hitman.linear_constraints.add(lin_expr=[[to_hit, [1] * len(to_hit)]], senses=['G'], rhs=[1], names=['sid{0}'.format(sid)])

        # optimization criterion
        if self.options.weighted:
            hitman.objective.set_linear([(vnames[rid], len(rule) + 1) for rid, rule in enumerate(self.rules)])
        else:
            hitman.objective.set_linear([(vnames[rid], 1) for rid, rule in enumerate(self.rules)])

        hitman.objective.set_sense(hitman.objective.sense.minimize)

        if self.options.pdump:
            fname = 'cover{0}.{1}@{2}.lp'.format(self.target, os.getpid(), socket.gethostname())
            hitman.write(fname)

        # and the cover is...
        hitman.solve()
        model, self.cover = hitman.solution, []
        for rid, v in enumerate(vnames, 1):
            if int(model.get_values(v)) > 0:
                self.cover.append(rid)

        self.cost += int(hitman.solution.get_objective_value())

        if self.options.weighted:
            self.cost -= len(self.cover)

        # cleaning up
        for sid in self.cluster:
            hitman.linear_constraints.delete('sid{0}'.format(sid))

    def compute_gurobi(self):
        """
            Cover samples for all labels using Gurobi.
        """

        assert gurobi_present, 'Gurobi is unavailable'

        if self.options.verb:
            print('c2 (using gurobi)')

        # a hack to disable license file logging
        stdout = sys.stdout
        sys.stdout = open(os.devnull, 'w')

        # initializing the solver
        hitman = gurobi.Model()

        # restoring sys.stdout
        sys.stdout = stdout

        # turning logger off
        hitman.Params.OutputFlag = 0
        hitman.Params.LogToConsole = 0

        # variables
        vnames = []
        prvars = []
        for i, rule in enumerate(self.rules):
            vnames.append('p_{0}'.format(i + 1))
            if self.options.weighted:
                prvars.append(hitman.addVar(vtype=gurobi.GRB.BINARY,
                    name=vnames[i], obj=len(rule) + 1))
            else:
                prvars.append(hitman.addVar(vtype=gurobi.GRB.BINARY,
                    name=vnames[i], obj=1))

        # hard constraints
        for sid in self.cluster:  # for every sample in cluster
            to_hit = []

            for rid, rule in enumerate(self.rules):
                if rule.issubset(self.samps[sid]):
                    to_hit.append(prvars[rid])

            hitman.addConstr(lhs=gurobi.quicksum(1 * v for v in to_hit),
                    sense=gurobi.GRB.GREATER_EQUAL,
                    rhs=1,
                    name='sid{0}'.format(sid))

        if self.options.pdump:
            fname = 'cover{0}.{1}@{2}.lp'.format(self.target, os.getpid(), socket.gethostname())
            hitman.write(fname)

        # and the cover is...
        hitman.optimize()
        self.cover = []
        for rid, rule in enumerate(prvars, 1):
            if int(rule.X) > 0:
                self.cover.append(rid)

        self.cost += int(hitman.objVal)

        if self.options.weighted:
            self.cost -= len(self.cover)

        # cleaning up
        for sid in self.cluster:
            c = hitman.getConstrByName('sid{0}'.format(sid))
            hitman.remove(c)

        hitman.remove(hitman.getVars())
