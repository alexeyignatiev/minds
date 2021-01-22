#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## mxsatl.py
##
##  Created on: May 7, 2020
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from __future__ import print_function
import collections
import decimal
import itertools
import math
from minds.rule import Rule
from minds.satr import SATRules
import os
from pysat.card import *
from pysat.examples.lbx import LBX
from pysat.examples.rc2 import RC2, RC2Stratified
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
import resource
import socket
import six
from six.moves import range
import sys


#
#==============================================================================
class MaxSATLits(SATRules, object):
    """
        Class implementing the new SAT-based approach.
    """

    def __init__(self, data, options):
        """
            Constructor.
        """

        super(MaxSATLits, self).__init__(data, options)

        # total number of missclassifications
        self.nof_misses = 0

    def compute(self):
        """
            Compute a decision set by minimizing the number of rules.
        """

        self.cost = 0

        # depending on this option, we compute either one class or all of them
        if self.options.to_compute == 'best':
            computed = len(self.data.feats[-1])
            self.labels = sorted(self.samps.keys())
        elif self.options.to_compute == 'all':
            computed = 0
            self.labels = sorted(self.samps.keys())
        else:
            to_compute = self.options.to_compute.split(',')
            computed = len(self.data.feats[-1]) - len(to_compute)
            self.labels = [self.data.fvmap.dir[self.data.names[-1], c] for c in to_compute]

        # iterative over the number of terms
        nof_terms = {label: 1 for label in self.labels}
        self.time = 0.0

        # upper bounds
        self.ubounds = {label: sum(self.data.wghts) for label in self.labels}

        # the value of Lambda may be decimal or integer
        # depending on whether or not we target exact solving
        if self.options.approx:
            self.lambda_ = int(math.ceil(sum(self.data.wghts) * float(self.options.lambda_)))
        else:
            self.lambda_ = sum(self.data.wghts) * decimal.Decimal(self.options.lambda_)

        if self.options.verb:
            print('c1 1 rule == {0} misses'.format(1 / self.lambda_))

        while True:
            for label in self.labels:
                if self.covrs[label]:
                    continue

                # resetting the pool of ids
                self.reset_idpool()

                # the main part is encoding
                enc = self.encode(label, nof_terms=nof_terms[label])

                if self.options.verb:
                    print('c1 # of terms: {0}; enc: {1}v, {2}h, {3}s; (class = {4})'.format(nof_terms[label],
                        enc.nv, len(enc.hard), len(enc.soft), self.data.fvmap.opp[label][1]))

                if self.options.pdump:
                    fname = 'formula-class{0}-sz{1}.{2}@{3}.wcnf'.format(label,
                            nof_terms[label], os.getpid(), socket.gethostname())
                    enc.to_file(fname)

                # choosing the right MaxSAT solver
                MaxSAT = RC2Stratified if self.options.weighted else RC2

                with MaxSAT(enc, solver=self.options.solver,
                        adapt=self.options.am1, exhaust=self.options.exhaust,
                        minz=self.options.minz, trim=self.options.trim, ) as rc2:
                    model = rc2.compute()

                    if model:
                        model = [0] + model

                        nof_miss = sum([self.data.wghts[i] if model[self.miss(i + 1)] > 0 else 0 for i in range(len(self.data.samps))])
                        nof_used = sum([1 if model[self.unused(j + 1)] < 0 else 0 for j in range(self.nof_terms)])
                        cost = nof_used + int(math.ceil(nof_miss / self.lambda_))
                        self.ubounds[label] = min(cost, self.ubounds[label])

                        if self.options.verb:
                            print('c1 # of used: {0}; # of misses: {1} (out of {2}); ub: {3}'.format(nof_used, nof_miss, sum(self.data.wghts), self.ubounds[label]))

                        if self.ubounds[label] in (nof_terms[label], nof_used):
                            # either the formulation has reached the bound
                            # or the actual solution did

                            if self.options.opt:
                                model = [0] + self.optimize(enc, model)

                            self.extract_cover(label, model)
                            self.nof_misses += nof_miss

                            computed += 1
                            if computed >= len(self.data.feats[-1]):
                                self.stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_stime
                                self.ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - self.init_ctime
                                self.time = self.stime + self.ctime

                                # computing accuracy
                                nof_samps = sum(self.data.wghts)

                                if not hasattr(self.data, 'wghts_filt'):
                                    self.accy_tot = 100. - (100. * self.nof_misses) / nof_samps
                                else:
                                    self.accy = 100. - (100. * self.nof_misses) / nof_samps
                                    self.accy_tot = 100. - (100. * (self.nof_misses + self.data.wghts_filt)) / (nof_samps + self.data.wghts_filt)

                                return self.covrs
                        else:
                            nof_terms[label] += 1
                            # if 10 < self.ubounds[label] - nof_terms[label]:
                            #     if 10 < 2 * nof_terms[label]:
                            #         nof_terms[label] += 10
                            #     else:
                            #         nof_terms[label] *= 2
                            # else:
                            #     nof_terms[label] = self.ubounds[label]
                    else:
                        nof_terms[label] += 1

    def encode(self, label, nof_terms=1):
        """
            Encode the problem of computing a DS of size nof_terms.
        """

        self.nof_terms = nof_terms

        enc = WCNF()

        # all the hard clauses
        #
        # constraint 6 (relaxed with the unused variable)
        for j in range(1, self.nof_terms + 1):
            for r in range(1, self.nof_feats + 1):
                enc.append([-self.unused(j), self.svar(j, r)])

            enc.append([self.unused(j)] + [-self.svar(j, r) for r in range(1, self.nof_feats + 1)])

        # sort unused rules
        for j in range(1, self.nof_terms):
            enc.append([-self.unused(j), self.unused(j + 1)])

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
        other_labels = sorted(other_labels)
        for j in range(1, self.nof_terms + 1):
            for lb in other_labels:
                for q in self.samps[lb]:
                    cl = [self.unused(j), self.miss(q + 1)]  # the clause is relaxed

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
                cl = [self.unused(j)]

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

        # constraint 10
        for q in self.samps[label]:
            enc.append([self.miss(q + 1)] + [self.crvar(j, q + 1) for j in range(1, self.nof_terms + 1)])

        # at most one value can be chosen for a feature
        for feats in six.itervalues(self.ffmap.dir):
            if len(feats) > 2:
                for j in range(1, self.nof_terms + 1):
                    lits = [self.dvar0(j, r + 1) for r in feats]  # atmost1 can be true
                    onev = CardEnc.atmost(lits, top_id=enc.nv, encoding=self.options.enc)
                    enc.extend(onev.clauses)

        # soft clauses
        # minimizing the number of literals used
        for j in range(1, self.nof_terms + 1):
            enc.append([self.unused(j)], weight=self.lambda_)
        # minimizing the number of missclassifications
        for lb in self.labels:
            for q in self.samps[lb]:
                enc.append([-self.miss(q + 1)], weight=self.data.wghts[q])

        # there should be at least one rule for this class
        enc.append([-self.unused(1)])

        # saving comments
        for j in range(1, self.nof_terms + 1):
            for r in range(1, self.nof_feats + 1):
                enc.comments.append('c s({0}, {1}) => v{2}'.format(j, r, self.svar(j, r)))
                enc.comments.append('c l({0}, {1}) => v{2}'.format(j, r, self.lvar(j, r)))
                enc.comments.append('c d0({0}, {1}) => v{2}'.format(j, r, self.dvar0(j, r)))
                enc.comments.append('c d1({0}, {1}) => v{2}'.format(j, r, self.dvar1(j, r)))

            for q in range(len(self.data.samps)):
                enc.comments.append('c cr({0}, {1}) => v{2}'.format(j, q + 1, self.crvar(j, q + 1)))

        for j in range(1, self.nof_terms + 1):
            enc.comments.append('c u({0}) => v{1}'.format(j, self.unused(j)))

        for lb in self.labels:
            for q in self.samps[lb]:
                enc.comments.append('c m({0}) => v{1}'.format(q + 1, self.miss(q + 1)))

        for n, f in zip(self.data.names[:-1], self.data.feats[:-1]):
            for v in f:
                if self.data.fvmap.dir[(n, v)] > 0:
                    enc.comments.append('c {0} = {1} => positive'.format(n, v))
                else:
                    enc.comments.append('c {0} = {1} => negative'.format(n, v))

        return enc

    def unused(self, j):
        """
            True if literal at node j is unused.
        """

        return self.idpool.id('unused_{0}'.format(j))

    def miss(self, q):
        """
            True if instance i is missclassified.
        """

        return self.idpool.id('miss_{0}'.format(q))

    def optimize(self, formula, model):
        """
            Try to optimize the solution with a MaxSAT solver.
        """

        MaxSAT = RC2Stratified if self.options.weighted else RC2

        formula_new = WCNF()
        formula_new.extend(formula.hard)

        # hardening the soft clauses based on the model
        for j in range(1, self.nof_terms + 1):
            formula_new.append([model[self.unused(j)]])
        for lb in self.labels:
            for q in self.samps[lb]:
                formula_new.append([model[self.miss(q + 1)]])

        for j in range(1, self.nof_terms + 1):
            for r in range(1, self.nof_feats + 1):
                formula_new.append([-self.dvar1(j, r)], weight=1)
                formula_new.append([-self.dvar0(j, r)], weight=1)

        with MaxSAT(formula_new, solver=self.options.solver,
                adapt=self.options.am1, exhaust=self.options.exhaust,
                minz=self.options.minz, trim=self.options.trim, ) as rc2:
            model = rc2.compute()

        return model

    def extract_cover(self, label, model):
        """
            Extracts a resulting DS from a model returned by a SAT oracle.
        """

        for j in range(1, self.nof_terms + 1):
            premise = []
            if model[self.unused(j)] > 0:
                break

            for r in range(1, self.nof_feats + 1):
                if model[self.dvar0(j, r)] > 0:
                    id_orig = self.ffmap.opp[r - 1]
                    premise.append(id_orig)
                elif model[self.dvar1(j, r)] > 0:
                    id_orig = self.ffmap.opp[r - 1]
                    premise.append(-id_orig)

            # creating the rule
            rule = Rule(fvars=premise, label=label, mapping=self.data.fvmap)

            if self.options.verb:
                print('c1 cover:', str(rule))

            self.covrs[label].append(rule)
            self.cost += len(rule)

        return self.covrs
