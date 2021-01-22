#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## mxsatls.py
##
##  Created on: Apr 28, 2020
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from __future__ import print_function
import collections
import itertools
from minds.rule import Rule
from minds.satl import SATLits
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
class MaxSATLitsSep(SATLits, object):
    """
        Class implementing the new SAT-based approach.
    """

    def __init__(self, data, options):
        """
            Constructor.
        """

        super(MaxSATLitsSep, self).__init__(data, options)

    def compute(self):
        """
            Compute a smallest size decision set.
        """

        self.cost = 0

        # iterative over the number of literals
        nof_lits = 2
        self.time = 0.0

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

        while True:
            for label in self.labels:
                if self.covrs[label]:
                    continue

                # resetting the pool of ids
                self.reset_idpool()

                # the main part is encoding
                enc = self.encode(label, nof_lits=nof_lits)

                if self.options.verb:
                    print('c1 # of lits: {0}; enc: {1}v, {2}h, {3}s; (class = {4})'.format(nof_lits,
                            enc.nv, len(enc.hard), len(enc.soft), self.data.fvmap.opp[label][1]))

                if self.options.pdump:
                    fname = 'formula.{0}@{1}.wcnf'.format(os.getpid(), socket.gethostname())
                    enc.to_file(fname)

                with RC2(enc, solver=self.options.solver,
                        adapt=self.options.am1, exhaust=self.options.exhaust,
                        minz=self.options.minz, trim=self.options.trim) as rc2:
                    model = rc2.compute()

                    if model:
                        model = [0] + model

                        self.extract_cover(label, model)

                        computed += 1
                        if computed >= len(self.data.feats[-1]):
                            self.stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_stime
                            self.ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - self.init_ctime
                            self.time = self.stime + self.ctime

                            return self.covrs

            else:
                nof_lits *= 2

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

        # soft clauses
        for j in range(1, self.nof_lits + 1):
            enc.append([self.unused(j)], weight=1)

        # all the hard clauses

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
        enc.append([-self.leaf(1)])  # first node can't be a leaf

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
                        self.label(j, lb)])

        # coverage constraints
        for i in self.samps[label]:
            cl = []

            for j in range(1, self.nof_lits + 1):
                cvar = self.covered(j, i + 1)

                enc.append([-cvar, self.leaf(j)])
                enc.append([-cvar, self.reached(j, i + 1)])
                enc.append([cvar, -self.leaf(j), -self.reached(j, i + 1)])

                cl.append(cvar)

            enc.append(cl)

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

                        if self.options.verb:
                            print('c1 cover:', str(rule))

                        self.covrs[label].append(rule)
                        self.cost += len(rule)

                        premise = []
                    else:
                        id_orig = self.ffmap.opp[r - 1]

                        if model[self.sign(j)] * id_orig > 0:
                            premise.append(id_orig)
                        else:
                            premise.append(-id_orig)

        return self.covrs
