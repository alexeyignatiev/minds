#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## minds1.py
##
##  Created on: Jan 16, 2018
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from __future__ import print_function
import collections
import itertools
import math
from minds.rule import Rule
from minds.satr import SATRules
import os
from pysat.card import *
from pysat.examples.lbx import LBX
from pysat.examples.rc2 import RC2
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
import resource
import socket
import six
from six.moves import range
import sys


#
#==============================================================================
class MinDS1Rules(SATRules, object):
    """
        Class implementing the new SAT-based approach.
    """

    def __init__(self, data, options):
        """
            Constructor.
        """

        super(MinDS1Rules, self).__init__(data, options)

    def compute(self):
        """
            Solving procedure.
        """

        self.cost = 0

        # iterative over the number of terms
        nof_terms = 1
        self.time = 0.0

        # depending on this option, we compute either one class or all of them
        if self.options.to_compute == 'best':
            self.labels = sorted(self.samps.keys())
        elif self.options.to_compute == 'all':
            self.labels = sorted(self.samps.keys())
        else:
            to_compute = self.options.to_compute.split(',')
            self.labels = [self.data.fvmap.dir[self.data.names[-1], c] for c in to_compute]

        assert len(self.labels) > 1, 'Multiple labels needed'

        while True:
            # resetting the pool of ids
            self.reset_idpool()

            # the main part is encoding
            enc = self.encode(nof_terms=nof_terms)

            if self.options.verb:
                print('c1 # of terms: {0}; enc: {1}v, {2}c'.format(nof_terms,
                        enc.nv, len(enc.clauses)))

            if self.options.pdump:
                fname = 'formula.{0}@{1}.cnf'.format(os.getpid(), socket.gethostname())
                enc.to_file(fname)

            with Solver(name=self.options.solver, bootstrap_with=enc.clauses) as s:
                res = s.solve()

                if res:
                    if self.options.opt:
                        assumps = self.optimize(enc)
                        s.solve(assumptions=assumps)

                    self.extract_cover(s.get_model())

                    self.stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_stime
                    self.ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - self.init_ctime
                    self.time = self.stime + self.ctime

                    return self.covrs

            nof_terms += 1

    def encode(self, nof_terms=1):
        """
            Encode the problem of computing a DS of size nof_terms.
        """

        self.nof_terms = nof_terms
        self.nof_samps = len(self.samps)
        self.nof_labls = len(self.labels)

        enc = CNF()

        # constraint 11
        for j in range(1, self.nof_terms + 1):
            enc.append([-self.svar(j, r) for r in range(1, self.nof_feats + 1)])

        # constraint 12
        for j in range(1, self.nof_terms + 1):
            for r in range(1, self.nof_feats + 1):
                d0 = self.dvar0(j, r)
                p0 = [-self.svar(j, r), self.lvar(j, r)]

                enc.append([d0, -p0[0], -p0[1]])
                enc.append([-d0, p0[0]])
                enc.append([-d0, p0[1]])

                d1 = self.dvar1(j, r)
                p1 = [-self.svar(j, r), -self.lvar(j, r)]

                enc.append([d1, -p1[0], -p1[1]])
                enc.append([-d1, p1[0]])
                enc.append([-d1, p1[1]])

        # constraint 13
        for j in range(1, self.nof_terms + 1):
            for z in range(1, self.nof_labls + 1):
                for lb in self.labels:
                    # skip current class label
                    if lb == self.labels[z - 1]:
                        continue

                    for q in self.samps[lb]:
                        cl = [-self.cvar(j, z)]

                        shift = 0
                        for r in range(1, self.nof_feats + 1):
                            if r - 1 in self.data.vmiss[q]:
                                # this feature is missing in q'th sample
                                cl.append(-self.svar(j, r))
                                shift += 1
                            elif self.data.samps[q][r - 1 - shift] > 0:
                                cl.append(self.dvar1(j, r))
                            else:
                                cl.append(self.dvar0(j, r))

                        enc.append(cl)

        # constraint 14
        for j in range(1, self.nof_terms + 1):
            for z, lb in enumerate(self.labels, 1):
                for q in self.samps[lb]:
                    cr = self.crvar(j, q + 1)
                    cl = [-self.cvar(j, z)]

                    shift = 0
                    for r in range(1, self.nof_feats + 1):
                        if r - 1 in self.data.vmiss[q]:
                            # this feature is missing in q'th sample
                            cl.append(-self.svar(j, r))
                            shift += 1
                        elif self.data.samps[q][r - 1 - shift] > 0:
                            cl.append(self.dvar1(j, r))
                        else:
                            cl.append(self.dvar0(j, r))

                    enc.append([cr] + cl)
                    for l in cl:
                        enc.append([-cr, -l])

        # constraint 16
        for i in range(1, self.nof_terms + 1):
            for j in range(i + 1, self.nof_terms + 1):
                if self.nof_labls == 2:
                    enc.append([-self.tlvar(i, j, 1), -self.cvar(i, 1), self.cvar(j, 1)])
                    enc.append([-self.tlvar(i, j, 1), self.cvar(i, 1), -self.cvar(j, 1)])
                    enc.append([self.tlvar(i, j, 1), -self.cvar(i, 1), -self.cvar(j, 1)])
                    enc.append([self.tlvar(i, j, 1), self.cvar(i, 1), self.cvar(j, 1)])

                    lhs = -self.tlvar(i, j, 1)
                else:
                    lits = []
                    for z in range(1, self.nof_labls + 1):
                        enc.append([-self.tlvar(i, j, z), -self.cvar(i, z), self.cvar(j, z)])
                        enc.append([-self.tlvar(i, j, z), self.cvar(i, z), -self.cvar(j, z)])
                        enc.append([self.tlvar(i, j, z), -self.cvar(i, z), -self.cvar(j, z)])
                        enc.append([self.tlvar(i, j, z), self.cvar(i, z), self.cvar(j, z)])

                        enc.append([-self.tlvar(i, j, self.nof_labls + 1), self.tlvar(i, j, z)])
                        lits.append(-self.tlvar(i, j, z))

                    enc.append([self.tlvar(i, j, self.nof_labls + 1)] + lits)
                    lhs = -self.tlvar(i, j, self.nof_labls + 1)

                terms = []
                for r in range(1, self.nof_feats + 1):
                    # equality between l variables
                    enc.append([-self.trvar0(i, j, r), -self.lvar(i, r), self.lvar(j, r)])
                    enc.append([-self.trvar0(i, j, r), self.lvar(i, r), -self.lvar(j, r)])
                    enc.append([self.trvar0(i, j, r), -self.lvar(i, r), -self.lvar(j, r)])
                    enc.append([self.trvar0(i, j, r), self.lvar(i, r), self.lvar(j, r)])

                    # r-th term
                    t = self.trvar1(i, j, r)
                    enc.append([-t, -self.svar(i, r)])
                    enc.append([-t, -self.svar(j, r)])
                    enc.append([-t, -self.trvar0(i, j, r)])
                    enc.append([t, self.svar(i, r), self.svar(j, r), self.trvar0(i, j, r)])

                    terms.append(t)

                enc.append([-lhs] + terms)

        # symmetry breaking constraints
        if self.options.bsymm:
            self.add_bsymm(enc)

        # constraint 15
        if self.options.accuracy == 100.0:
            for label in self.labels:
                for q in self.samps[label]:
                    enc.append([self.crvar(j, q + 1) for j in range(1, self.nof_terms + 1)])
        else:
            allcv = []
            for label in self.labels:
                for q in self.samps[label]:
                    cv = self.cvvar(q + 1)
                    enc.append([-cv] + [self.crvar(j, q + 1) for j in range(1, self.nof_terms + 1)])

                    for j in range(1, self.nof_terms + 1):
                        enc.append([-self.crvar(j, q + 1), cv])

                    allcv.append(cv)

            cnum = int(math.ceil(self.options.accuracy * len(allcv) / 100.0))
            al = CardEnc.atleast(allcv, bound=cnum, top_id=enc.nv, encoding=self.options.enc)
            if al:
                enc.extend(al.clauses)

        # at most one value can be chosen for a feature
        for feats in six.itervalues(self.ffmap.dir):
            if len(feats) > 2:
                for j in range(1, self.nof_terms + 1):
                    lits = [self.dvar0(j, r + 1) for r in feats]  # atmost1 can be true
                    onev = CardEnc.atmost(lits, top_id=enc.nv, encoding=self.options.enc)
                    enc.extend(onev.clauses)

        # at most one class per rule can be used
        if self.nof_labls > 2:
            for j in range(1, self.nof_terms + 1):
                onelb = CardEnc.equals([self.cvar(j, z) for z in range(1, self.nof_labls + 1)], top_id=enc.nv, encoding=self.options.enc)
                enc.extend(onelb.clauses)

        # saving comments
        for j in range(1, self.nof_terms + 1):
            if self.nof_labls > 2:
                for z in range(1, self.nof_labls + 1):
                    enc.comments.append('c c({0}, {1}) => v{2}'.format(j, z, self.cvar(j, z)))

            for r in range(1, self.nof_feats + 1):
                enc.comments.append('c s({0}, {1}) => v{2}'.format(j, r, self.svar(j, r)))
                enc.comments.append('c l({0}, {1}) => v{2}'.format(j, r, self.lvar(j, r)))
                enc.comments.append('c d0({0}, {1}) => v{2}'.format(j, r, self.dvar0(j, r)))
                enc.comments.append('c d1({0}, {1}) => v{2}'.format(j, r, self.dvar1(j, r)))

            for q in range(len(self.data.samps)):
                enc.comments.append('c cr({0}, {1}) => v{2}'.format(j, q + 1, self.crvar(j, q + 1)))

        for n, f in zip(self.data.names[:-1], self.data.feats[:-1]):
            for v in f:
                if self.data.fvmap.dir[(n, v)] > 0:
                    enc.comments.append('c {0} = {1} => positive'.format(n, v))
                else:
                    enc.comments.append('c {0} = {1} => negative'.format(n, v))

        return enc

    def add_bsymm(self, enc):
        """
            Symmetry breaking constraints.
        """

        for j in range(2, self.nof_terms + 1):
            enc.append([self.eqvar(j, 0)])
            enc.append([-self.gtvar(j, 0)])
            enc.append([self.gtvar(j, self.nof_feats)])  # enforcing SBPs

            for r in range(1, self.nof_feats + 1):
                # constraint 11
                #
                # left-hand side
                lhs = -self.eqvar(j, r)

                # term1
                enc.append([-self.teqvar(j, r, 1), self.svar(j - 1, r)])
                enc.append([-self.teqvar(j, r, 1), -self.svar(j, r)])
                enc.append([self.teqvar(j, r, 1), -self.svar(j - 1, r), self.svar(j, r)])

                # term2
                enc.append([-self.teqvar(j, r, 2), -self.svar(j - 1, r)])
                enc.append([-self.teqvar(j, r, 2), self.svar(j, r)])
                enc.append([self.teqvar(j, r, 2), self.svar(j - 1, r), -self.svar(j, r)])

                # term3
                enc.append([-self.teqvar(j, r, 3), self.dvar1(j - 1, r)])
                enc.append([-self.teqvar(j, r, 3), self.dvar0(j, r)])
                enc.append([self.teqvar(j, r, 3), -self.dvar1(j - 1, r), -self.dvar0(j, r)])

                # term4
                enc.append([-self.teqvar(j, r, 4), self.dvar0(j - 1, r)])
                enc.append([-self.teqvar(j, r, 4), self.dvar1(j, r)])
                enc.append([self.teqvar(j, r, 4), -self.dvar0(j - 1, r), -self.dvar1(j, r)])

                # right-hand side
                cl = [-self.eqvar(j, r - 1),
                        self.teqvar(j, r, 1),
                        self.teqvar(j, r, 2),
                        self.teqvar(j, r, 3),
                        self.teqvar(j, r, 4)]

                # final clauses
                enc.append([-lhs] + cl)
                for l in cl:
                    enc.append([-l, lhs])

                # constraint 12
                #
                # left-hand side
                lhs = self.gtvar(j, r)

                # term1
                enc.append([-self.tgtvar(j, r, 1), self.eqvar(j, r - 1)])
                enc.append([-self.tgtvar(j, r, 1), -self.svar(j - 1, r)])
                enc.append([-self.tgtvar(j, r, 1), self.svar(j, r)])
                enc.append([self.tgtvar(j, r, 1), -self.eqvar(j, r - 1), self.svar(j - 1, r), -self.svar(j, r)])

                # term2
                enc.append([-self.tgtvar(j, r, 2), self.eqvar(j, r - 1)])
                enc.append([-self.tgtvar(j, r, 2), self.dvar1(j - 1, r)])
                enc.append([-self.tgtvar(j, r, 2), self.dvar0(j, r)])
                enc.append([self.tgtvar(j, r, 2), -self.eqvar(j, r - 1), -self.dvar1(j - 1, r), -self.dvar0(j, r)])

                # right-hand side
                cl = [self.gtvar(j, r - 1),
                        self.tgtvar(j, r, 1),
                        self.tgtvar(j, r, 2)]

                # final clauses
                enc.append([-lhs] + cl)
                for l in cl:
                    enc.append([-l, lhs])

    def svar(self, j, r):
        """
            True iff literal on feature r is to be skipped for rule j.
        """

        return self.idpool.id('s_{0}_{1}'.format(j, r))

    def lvar(self, j, r):
        """
            Literal on feature r for rule j (if the feature is not skipped).
        """

        return self.idpool.id('l_{0}_{1}'.format(j, r))

    def cvar(self, j, z):
        """
            True iff rule j is associated with class m.
        """

        if self.nof_labls == 2:
            return (1 if z == 1 else -1) * self.idpool.id('c_{0}_1'.format(j))

        return self.idpool.id('c_{0}_{1}'.format(j, z))

    def dvar0(self, j, r):
        """
            True iff rule j discriminates feature r on value 0.
        """

        return self.idpool.id('d0_{0}_{1}'.format(j, r))

    def dvar1(self, j, r):
        """
            True iff rule j discriminates feature r on value 1.
        """

        return self.idpool.id('d1_{0}_{1}'.format(j, r))

    def crvar(self, j, q):
        """
            True iff (used) rule j covers sample q.
        """

        return self.idpool.id('cr_{0}_{1}'.format(j, q))

    def tlvar(self, i, j, k):
        """
            Tseitin variable encoding equality of LHS of constraint 16.
        """

        return self.idpool.id('tl_{0}_{1}_{2}'.format(i, j, k))

    def trvar0(self, i, j, r):
        """
            Tseitin variable encoding equality of the RHS of constraint 16.
        """

        return self.idpool.id('tr0_{0}_{1}_{2}'.format(i, j, r))

    def trvar1(self, i, j, r):
        """
            Tseitin variable encoding the RHS of constraint 16.
        """

        return self.idpool.id('tr1_{0}_{1}_{2}'.format(i, j, r))

    def eqvar(self, j, r):
        """
            Equality variables for symmetry breaking.
        """

        return self.idpool.id('eq_{0}_{1}'.format(j, r))

    def gtvar(self, j, r):
        """
            'Greater than' variables for symmetry breaking.
        """

        return self.idpool.id('gt_{0}_{1}'.format(j, r))

    def teqvar(self, j, r, i):
        """
            Equality-related Tseitin variables for symmetry breaking.
        """

        return self.idpool.id('te_{0}_{1}_{2}'.format(j, r, i))

    def tgtvar(self, j, r, i):
        """
            'Greater than'-related Tseitin variables for symmetry breaking.
        """

        return self.idpool.id('tg_{0}_{1}_{2}'.format(j, r, i))

    def optimize(self, enc):
        """
            Try to optimize the solution with a MaxSAT solver.
        """

        # all d0 and d1 variables (for computing the complement --- MSS)
        all_vars = set([])

        # MaxSAT formula to work with
        formula = WCNF()

        # hard clauses
        for cl in enc.clauses:
            formula.append(cl)

        for j in range(1, self.nof_terms + 1):
            for r in range(1, self.nof_feats + 1):
                formula.append([-self.dvar1(j, r)], 1)
                formula.append([-self.dvar0(j, r)], 1)

                all_vars.add(self.dvar1(j, r))
                all_vars.add(self.dvar0(j, r))

        if self.options.approx:
            hitman = LBX(formula, use_cld=self.options.use_cld,
                    solver_name=self.options.solver)

            hses = []
            for i, hs in enumerate(hitman.enumerate()):
                hitman.block(hs)
                hses.append(hs)

                if i + 1 == self.options.approx:
                    break

            hs = list(map(lambda v: -formula.soft[v - 1][0], min(hses, key=lambda x: len(x))))
            hitman.delete()
        else:
            hitman = RC2(formula, solver=self.options.solver, adapt=True,
                    exhaust=True, incr=False, minz=False, trim=self.options.trim)

            hs = list(filter(lambda v: v > 0 and v in all_vars, hitman.compute()))
            hitman.delete()

        return sorted([-v for v in all_vars.difference(set(hs))])

    def extract_cover(self, model):
        """
            Extracts a resulting DS from a model returned by a SAT oracle.
        """

        for j in range(1, self.nof_terms + 1):
            premise = []
            for r in range(1, self.nof_feats + 1):
                if model[self.dvar0(j, r) - 1] > 0:
                    id_orig = self.ffmap.opp[r - 1]
                    premise.append(id_orig)
                elif model[self.dvar1(j, r) - 1] > 0:
                    id_orig = self.ffmap.opp[r - 1]
                    premise.append(-id_orig)

            if self.nof_labls == 2:
                label = self.labels[0 if model[self.cvar(j, 1) - 1] > 0 else 1]
            else:
                for z, lb in enumerate(self.labels, 1):
                    if model[self.cvar(j, z) - 1] > 0:
                        label = lb
                        break
                else:
                    assert False, 'No class label found in the model'

            # creating the rule
            rule = Rule(fvars=premise, label=label, mapping=self.data.fvmap)

            if self.options.verb:
                print('c1 cover:', str(rule))

            self.covrs[label].append(rule)
            self.cost += len(rule)

        return self.covrs
