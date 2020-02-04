#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## sat.py
##
##  Created on: Jan 9, 2018
##      Author: Alexey S. Ignatiev
##      E-mail: aignatiev@ciencias.ulisboa.pt
##

#
#==============================================================================
from __future__ import print_function
import collections
import itertools
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
class SATMinMode(object):
    """
        Mode of operation (approach).
    """

    rules    = 0
    literals = 1
    multiobj = 2
    blo      = 3


#
#==============================================================================
class SAT(object):
    """
        Class implementing the new SAT-based approach.
    """

    def __init__(self, data, options):
        """
            Constructor.
        """

        self.init_stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime
        self.init_ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime

        self.data = data
        self.options = options

        # init variable id pool
        self.reset_idpool()

        # samples divided into classes
        self.samps = {self.data.fvmap.dir[(self.data.names[-1], v)]: [] for v in self.data.feats[-1]}

        # covers by class
        self.covrs = {self.data.fvmap.dir[(self.data.names[-1], v)]: [] for v in self.data.feats[-1]}

        for i, s in enumerate(self.data.samps):
                self.samps[s[-1]].append(i)

        # binarize dataset if necessary
        self.binarize()

        # get missing values for each sample
        self.get_missing()

        self.cost = 0

    def binarize(self):
        """
            Do one-hot encoding.
        """

        FFMap = collections.namedtuple('FFMap', ['dir', 'opp'])
        self.ffmap = FFMap(dir={}, opp={})

        curr_id = 0
        vfmap = {}  # mapping from a feature id to a list of feature ids
        for r, (name, feats) in enumerate(zip(self.data.names[:-1], self.data.feats[:-1])):
            fgroup = []
            if len(feats) != 2:
                vars_ = [self.data.fvmap.dir[name, v] for v in feats]
                for i, var in enumerate(vars_):
                    vfmap[var] = [-v for v in vars_]
                    vfmap[var][i] = var

                    self.ffmap.opp[i + curr_id] = var
                    fgroup.append(i + curr_id)

                curr_id += len(feats)
            else:
                var = self.data.fvmap.dir[name, list(feats)[0]]
                vfmap[var] = [var]
                vfmap[-var] = [-var]
                self.ffmap.opp[curr_id] = var
                fgroup.append(curr_id)

                curr_id += 1

            self.ffmap.dir[r] = fgroup

        # rewriting samples
        for i in range(len(self.data.samps)):
            samp, out = self.data.samps[i][:-1], self.data.samps[i][-1]

            self.data.samps[i] = []
            for l in samp:
                self.data.samps[i].extend(vfmap[l])

            self.data.samps[i].append(out)

        self.nof_feats = curr_id

    def get_missing(self):
        """
            Get a list of missing values for each sample.
        """

        self.data.vmiss = []

        for s in self.data.samps:
            missing = []

            if len(s) < self.nof_feats + 1:
                r = i = 0
                while i < len(s) - 1:
                    if r in self.ffmap.dir[self.data.nm2id[self.data.fvmap.opp[abs(s[i])][0]]]:
                        i += 1
                    else:
                        missing.append(r)

                    r += 1

                # adding the rest of the features
                missing.extend(range(r, self.nof_feats))

            # set is needed for testing inclusion
            self.data.vmiss.append(set(missing))

    def reset_idpool(self):
        """
            Reset the pool of variable ids.
        """

        self.idpool = itertools.count(start=1)
        self.vars = collections.defaultdict(lambda: next(self.idpool))

    def compute(self):
        """
            Choose a method to compute a decision set.
        """

        if self.options.mode == SATMinMode.rules:
            return self.compute_minrules()
        elif self.options.mode == SATMinMode.literals:
            return self.compute_minlits()
        elif self.options.mode == SATMinMode.multiobj:
            return self.compute_multiobj()
        else:
            assert 0, 'Non-existing minimization mode chosen'

    def compute_minrules(self):
        """
            Compute a decision set by minimizing the number of rules.
        """

        self.cost = 0

        # iterative over the number of terms
        nof_terms = 1
        self.time = 0.0

        # depending on this option, we compute either one class or all of them
        if self.options.to_compute == 'best':
            computed = len(self.data.feats[-1])
            self.labels = list(self.samps.keys())
        elif self.options.to_compute == 'all':
            computed = 0
            self.labels = list(self.samps.keys())
        else:
            to_compute = self.options.to_compute.split(',')
            computed = len(self.data.feats[-1]) - len(to_compute)
            self.labels = [self.data.fvmap.dir[self.data.names[-1], c] for c in to_compute]

        while True:
            for label in self.labels:
                if self.covrs[label]:
                    continue

                # resetting the pool of ids
                self.reset_idpool()

                # the main part is encoding
                enc = self.encode(label, nof_terms=nof_terms)

                if self.options.verb:
                    print('c1 # of terms: {0}; enc: {1}v, {2}c; (class = {3})'.format(nof_terms,
                        enc.nv, len(enc.clauses), self.data.fvmap.opp[label][1]))

                if self.options.pdump:
                    fname = 'formula.{0}@{1}.cnf'.format(os.getpid(), socket.gethostname())
                    enc.to_file(fname)

                with Solver(name=self.options.solver, bootstrap_with=enc.clauses) as s:
                    res = s.solve()

                    if res:
                        model = s.get_model()

                        if self.options.opt:
                            model = self.optimize(enc)

                        self.extract_cover(label, model)

                        computed += 1
                        if computed >= len(self.data.feats[-1]):
                            self.stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_stime
                            self.ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - self.init_ctime
                            self.time = self.stime + self.ctime

                            return self.covrs
            else:
                nof_terms += 1

    def compute_minlits(self):
        """
            Compute a decision set by minimizing the number of literals.
        """

        assert 0, 'Not yet implemented'

    def compute_multiobj(self):
        """
            Compute a decision set by minimizing the number of rules
            and literals. Do some kind of multi-criteria optimization.
        """

        assert 0, 'Not yet implemented'

        self.cost = 0

        # iterative over the number of terms
        nof_terms = 1
        self.time = 0.0

        # depending on this option, we compute either one class or all of them
        if self.options.to_compute == 'all':
            computed = 0
            self.labels = list(self.samps.keys())
        else:
            to_compute = self.options.to_compute.split(',')
            computed = len(self.data.feats[-1]) - len(to_compute)
            self.labels = [self.data.fvmap.dir[self.data.names[-1], c] for c in to_compute]

        for label in self.labels:
            nof_terms = 1

            while True:
                # resetting the pool of ids
                self.reset_idpool()

                # the main part is encoding
                enc = self.encode(label, nof_terms=nof_terms)

                if self.options.verb:
                    print('c1 # of terms: {0}; enc: {1}v, {2}c; (class = {3})'.format(nof_terms,
                        enc.nv, len(enc.clauses), self.data.fvmap.opp[label][1]))

                if self.options.pdump:
                    fname = 'formula.{0}@{1}.cnf'.format(os.getpid(), socket.gethostname())
                    enc.to_file(fname)

                with Solver(name=self.options.solver, bootstrap_with=enc.clauses) as s:
                    if s.solve():
                        model = s.get_model()

                        if self.options.opt:
                            model = self.optimize(enc)

                        self.extract_cover(label, model)
                        break
                    else:
                        nof_terms *= 2

        self.stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_stime
        self.ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - self.init_ctime
        self.time = self.stime + self.ctime

        return self.covrs

    def encode(self, label, nof_terms=1):
        """
            Encode the problem of computing a DS of size nof_terms.
        """

        self.nof_terms = nof_terms
        self.nof_samps = len(self.samps)

        enc = CNF()

        # constraint 6
        for j in range(1, self.nof_terms + 1):
            enc.append([-self.svar(j, r) for r in range(1, self.nof_feats + 1)])

        # constraint 7
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

        # constraint 8
        if len(self.labels) == 1:  # distinguish one class from all the others
            other_labels = set(self.samps.keys())
        else:  # distinguish the classes under question only
            other_labels = set(self.labels)
        other_labels.remove(label)
        other_labels = list(other_labels)
        for j in range(1, self.nof_terms + 1):
            for lb in other_labels:
                for q in self.samps[lb]:
                    cl = []

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

        # constraint 9
        for j in range(1, self.nof_terms + 1):
            for q in self.samps[label]:
                cr = self.crvar(j, q + 1)
                cl = []

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

        # symmetry breaking constraints
        if self.options.bsymm:
            self.add_bsymm(enc)

        # constraint 10
        for q in self.samps[label]:
            enc.append([self.crvar(j, q + 1) for j in range(1, self.nof_terms + 1)])

        # at most one value can be chosen for a feature
        for feats in six.itervalues(self.ffmap.dir):
            if len(feats) > 2:
                for j in range(1, self.nof_terms + 1):
                    lits = [self.dvar0(j, r + 1) for r in feats]  # atmost1 can be true
                    onev = CardEnc.atmost(lits, top_id=enc.nv, encoding=self.options.enc)
                    enc.extend(onev.clauses)

        # saving comments
        for j in range(1, self.nof_terms + 1):
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

        return self.vars['s_{0}_{1}'.format(j, r)]

    def lvar(self, j, r):
        """
            Literal on feature r for rule j (if the feature is not skipped).
        """

        return self.vars['l_{0}_{1}'.format(j, r)]

    def dvar0(self, j, r):
        """
            True iff rule j discriminates feature r on value 0.
        """

        return self.vars['d0_{0}_{1}'.format(j, r)]

    def dvar1(self, j, r):
        """
            True iff rule j discriminates feature r on value 1.
        """

        return self.vars['d1_{0}_{1}'.format(j, r)]

    def crvar(self, j, q):
        """
            True iff (used) rule j covers sample q.
        """

        return self.vars['cr_{0}_{1}'.format(j, q)]

    def cvvar(self, q):
        """
            True iff sample q is covered.
        """

        return self.vars['cv_{0}'.format(q)]

    def eqvar(self, j, r):
        """
            Equality variables for symmetry breaking.
        """

        return self.vars['eq_{0}_{1}'.format(j, r)]

    def gtvar(self, j, r):
        """
            'Greater than' variables for symmetry breaking.
        """

        return self.vars['gt_{0}_{1}'.format(j, r)]

    def teqvar(self, j, r, i):
        """
            Equality-related Tseitin variables for symmetry breaking.
        """

        return self.vars['te_{0}_{1}_{2}'.format(j, r, i)]

    def tgtvar(self, j, r, i):
        """
            'Greater than'-related Tseitin variables for symmetry breaking.
        """

        return self.vars['tg_{0}_{1}_{2}'.format(j, r, i)]

    def get_topid(self):
        """
            Get a top variable id.
        """

        return int(repr(self.idpool)[6:-1]) - 1

    def optimize(self, enc):
        """
            Try to optimize the solution with a MaxSAT solver.
        """

        # a dummy model (everything is deselected)
        model = [-v for v in range(enc.nv)]
        all_vars = set()

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

        # filling the model with the right values
        for e in hs:
            model[e - 1] = e

        return model

    def extract_cover(self, label, model):
        """
            Extracts a resulting DS from a model returned by a SAT oracle.
        """

        for j in range(1, self.nof_terms + 1):
            premise = []
            for r in range(1, self.nof_feats + 1):
                if model[self.dvar0(j, r) - 1] > 0:
                    id_orig = self.ffmap.opp[r - 1]
                    name, val = self.data.fvmap.opp[id_orig]
                    premise.append('\'{0}: {1}\''.format(name, val))
                elif model[self.dvar1(j, r) - 1] > 0:
                    id_orig = self.ffmap.opp[r - 1]
                    name, val = self.data.fvmap.opp[id_orig]
                    premise.append('not \'{0}: {1}\''.format(name, val))

            if self.options.verb:
                print('c1 cover:', '{0} => {1}'.format(', '.join(premise), ': '.join(self.data.fvmap.opp[label])))

            self.covrs[label].append(premise)
            self.cost += len(premise)

        return self.covrs
