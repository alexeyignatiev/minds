#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## mxsatsp.py
##
##  Created on: Apr 28, 2020
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
from minds.satl import SATLits
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
class MaxSATSparse(SATLits, object):
    """
        Class implementing the new SAT-based approach.
    """

    def __init__(self, data, options):
        """
            Constructor.
        """

        super(MaxSATSparse, self).__init__(data, options)

        # total number of missclassifications
        self.nof_misses = 0

    def compute(self):
        """
            Compute a smallest size decision set.
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

        # iterative over the number of literals
        nof_lits = {label: 2 for label in self.labels}
        self.time = 0.0

        # upper bounds
        self.ubounds = {label: (self.nof_feats + 1) * sum(self.data.wghts) for label in self.labels}

        # the value of Lambda may be decimal or integer
        # depending on whether or not we target exact solving
        if self.options.approx:
            self.lambda_ = int(math.ceil(sum(self.data.wghts) * float(self.options.lambda_)))
        else:
            self.lambda_ = sum(self.data.wghts) * decimal.Decimal(self.options.lambda_)

        if self.options.lambda_adaptive:
            self.lambda_ /= self.nof_feats

        if self.options.verb:
            print('c1 1 lit == {0} misses'.format(1 / self.lambda_))

        while True:
            for label in self.labels:
                # print('lits', nof_lits)
                # print('ubs', self.ubounds)
                # print('feats', self.nof_feats, len(self.samps[label]))
                if self.covrs[label]:
                    continue

                # resetting the pool of ids
                self.reset_idpool()

                # the main part is encoding
                enc = self.encode(label, nof_lits=nof_lits[label])

                if self.options.verb:
                    print('c1 # of lits: {0}; enc: {1}v, {2}h, {3}s; (class = {4})'.format(nof_lits[label],
                            enc.nv, len(enc.hard), len(enc.soft), self.data.fvmap.opp[label][1]))

                if self.options.pdump:
                    fname = 'formula-class{0}-sz{1}.{2}@{3}.wcnf'.format(label,
                            nof_lits[label], os.getpid(), socket.gethostname())
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
                        nof_used = sum([1 if model[self.unused(j + 1)] < 0 else 0 for j in range(self.nof_lits)])
                        # cost = nof_used + math.ceil(nof_miss / self.lambdas[label])
                        cost = nof_used + int(math.ceil(nof_miss / self.lambda_))
                        self.ubounds[label] = min(cost, self.ubounds[label])

                        if self.options.verb:
                            print('c1 # of used: {0}; # of misses: {1} (out of {2}); ub: {3}'.format(nof_used, nof_miss, sum(self.data.wghts), self.ubounds[label]))

                        if self.ubounds[label] in (nof_lits[label], nof_used):
                            # either the formulation has reached the bound
                            # or the actual solution did
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
                            if 10 < self.ubounds[label] - nof_lits[label]:
                                if 10 < 2 * nof_lits[label]:
                                    nof_lits[label] += 10
                                else:
                                    nof_lits[label] *= 2
                            else:
                                nof_lits[label] = self.ubounds[label]
                    else:
                        nof_lits[label] += 1

    def encode(self, label, nof_lits=1):
        """
            Encode the problem of computing a DS of size nof_lits.
        """

        self.nof_lits = nof_lits
        self.nof_samps = len(self.data.samps)
        self.nof_labls = len(self.labels)

        if len(self.labels) == 1:  # distinguish one class from all the others
            other_labels = set(self.samps.keys())
        else:  # distinguish the classes under question only
            other_labels = set(self.labels)
        other_labels.remove(label)
        other_labels = sorted(other_labels)

        for j in range(1, self.nof_lits + 1):
            for r in range(1, self.nof_feats + 2):
                self.feat(j, r)
        for j in range(1, self.nof_lits + 1):
            self.sign(j)
        for j in range(1, self.nof_lits + 1):
            self.leaf(j)

        enc = WCNF()

        # all the hard clauses
        #
        # exactly one feature per node (including class/label)
        for j in range(1, self.nof_lits + 1):
            feats = [self.feat(j, r) for r in range(1, self.nof_feats + 2)] + [self.unused(j)]
            one = CardEnc.equals(lits=feats, vpool=self.idpool, encoding=self.options.enc)
            enc.extend(one)

        # at most one class/label per node
        for j in range(1, self.nof_lits + 1):
            labels = [self.label(j, z) for z in self.labels]
            am1 = CardEnc.atmost(lits=labels, vpool=self.idpool, encoding=self.options.enc)
            enc.extend(am1)

            # the model is split,
            # i.e. we currently target only rules for this concrete class
            enc.append([self.label(j, label)])

        # propagation of unused literals
        for j in range(1, self.nof_lits):
            enc.append([-self.unused(j), self.unused(j + 1)])

        # leaf constraints
        # this disallows empty (default) rules and thus is disabled
        # enc.append([-self.leaf(1)])  # first node can't be a leaf

        # last leaf
        for j in range(1, self.nof_lits):
            enc.append([-self.unused(j + 1), self.unused(j), self.leaf(j)])
        enc.append([self.leaf(self.nof_lits), self.unused(self.nof_lits)])

        # everything is reachable at node 1
        for lb in self.labels:
            for i in self.samps[lb]:
                enc.append([self.reached(1, i + 1)])

        # reachability propagation
        for j in range(1, self.nof_lits):
            for lb in self.labels:
                for i in self.samps[lb]:
                    aij = self.agree(j, i + 1)

                    cl, shift = [], 0
                    for r in range(1, self.nof_feats + 1):
                        if r - 1 in self.data.vmiss[i]:
                            # this feature is missing in i'th sample
                            shift += 1
                        else:
                            # a = self.agree(j, i + 1, r)  # node j agrees with sample i on feature r
                            f = self.feat(j, r)  # feature r decided in node j
                            s = self.sign(j)  # polarity of node j

                            if self.data.samps[i][r - 1 - shift] > 0:
                                a = self.sets1(j, r)
                                if a > enc.nv:
                                    enc.extend([[-a, f], [-a,  s], [a, -f, -s]])
                            else:
                                a = self.sets0(j, r)
                                if a > enc.nv:
                                    enc.extend([[-a, f], [-a, -s], [a, -f,  s]])

                            cl.append(a)

                    enc.append([-aij] + cl)
                    for l in cl:
                        enc.append([aij, -l])

                    cur = self.reached(j,     i + 1)  # node j is reachable for sample i
                    new = self.reached(j + 1, i + 1)  # node j + 1 reachable for sample i

                    enc.append([-new,  self.leaf(j), cur])
                    enc.append([-new,  self.leaf(j), aij])
                    enc.append([ new, -self.leaf(j)])
                    enc.append([ new, -cur, -aij])

        # correctness of leafs
        for j in range(1, self.nof_lits + 1):
            for lb in self.labels:
                for i in self.samps[lb]:
                    enc.append([-self.leaf(j), -self.reached(j, i + 1),
                        self.label(j, lb), self.miss(i + 1)])

        # coverage constraints
        for i in self.samps[label]:
            cl = [self.miss(i + 1)]  # here the clause is relaxed

            for j in range(1, self.nof_lits + 1):
                cvar = self.covered(j, i + 1)

                enc.append([-cvar, self.leaf(j)])
                enc.append([-cvar, self.reached(j, i + 1)])
                enc.append([cvar, -self.leaf(j), -self.reached(j, i + 1)])

                cl.append(cvar)

            enc.append(cl)

        # soft clauses
        # minimizing the number of literals used
        for j in range(1, self.nof_lits + 1):
            # enc.append([self.unused(j)], weight=self.lambdas[label])
            enc.append([self.unused(j)], weight=self.lambda_)
        # minimizing the number of missclassifications
        for lb in self.labels:
            for i in self.samps[lb]:
                enc.append([-self.miss(i + 1)], weight=self.data.wghts[i])

        # there should be at least two literals in the decision set
        # since u_j variables are sorted, we know that they are u1 and u2
        # enc.extend([[-self.unused(1)], [-self.unused(2)]])

        # the previous constraints disallowed empty (default) rules
        # and so this one looks better
        enc.extend([[-self.unused(1)]])

        # symmetry breaking
        if self.options.bsymm:
            self.add_bsymm(enc)

        for v, o in self.idpool.id2obj.items():
            enc.comments.append('c {0} <=> {1}'.format(o, v))

        return enc

    def unused(self, j):
        """
            True if literal at node j is unused.
        """

        return self.idpool.id('unused_{0}'.format(j))

    def miss(self, i):
        """
            True if instance i is missclassified.
        """

        return self.idpool.id('miss_{0}'.format(i))

    def extract_cover(self, label, model):
        """
            Extracts a resulting DS from a model returned by a SAT oracle.
        """

        premise = []

        for j in range(1, self.nof_lits + 1):
            for r in range(1, self.nof_feats + 2):
                if model[self.feat(j, r)] > 0:
                    if model[self.leaf(j)] > 0:
                        # creating the rule
                        rule = Rule(fvars=premise, label=label,
                                mapping=self.data.fvmap)

                        self.covrs[label].append(rule)
                        self.cost += len(rule)

                        if self.options.verb:
                            if premise:  # if not a default rule (those aren't printed here)
                                print('c1 cover:', str(rule))

                        premise = []
                    else:
                        id_orig = self.ffmap.opp[r - 1]

                        if model[self.sign(j)] * id_orig > 0:
                            premise.append(id_orig)
                        else:
                            premise.append(-id_orig)

        return self.covrs
