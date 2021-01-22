#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## satl.py
##
##  Created on: Mar 20, 2020
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from __future__ import print_function
import collections
import itertools
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
class SATLits(SATRules, object):
    """
        Class implementing the new SAT-based approach.
    """

    def __init__(self, data, options):
        """
            Constructor.
        """

        super(SATLits, self).__init__(data, options)

    def compute(self):
        """
            Compute a smallest size decision set.
        """

        self.cost = 0

        # iterative over the number of literals
        nof_lits = 1
        self.time = 0.0

        # depending on this option, we compute either one class or all of them
        if self.options.to_compute == 'best':
            self.labels = sorted(self.samps.keys())
        elif self.options.to_compute == 'all':
            self.labels = sorted(self.samps.keys())
        else:
            to_compute = self.options.to_compute.split(',')
            self.labels = [self.data.fvmap.dir[self.data.names[-1], c] for c in to_compute]

        while True:
            # resetting the pool of ids
            self.reset_idpool()

            # the main part is encoding
            enc = self.encode(nof_lits=nof_lits)

            if self.options.verb:
                print('c1 # of lits: {0}; enc: {1}v, {2}c'.format(nof_lits,
                        enc.nv, len(enc.clauses)))

            if self.options.pdump:
                fname = 'formula-sz{0}.{1}@{2}.cnf'.format(nof_lits, os.getpid(), socket.gethostname())
                enc.to_file(fname)

            with Solver(name=self.options.solver, bootstrap_with=enc.clauses) as s:
                res = s.solve()

                if res:
                    model = [0] + s.get_model()

                    self.extract_cover(model)

                    self.stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_stime
                    self.ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - self.init_ctime
                    self.time = self.stime + self.ctime

                    return self.covrs

            nof_lits += 1

    def encode(self, nof_lits=1):
        """
            Encode the problem of computing a DS of size nof_lits.
        """

        self.nof_lits = nof_lits
        self.nof_samps = len(self.data.samps)
        self.nof_labls = len(self.labels)

        for j in range(1, self.nof_lits + 1):
            for r in range(1, self.nof_feats + 2):
                self.feat(j, r)
        for j in range(1, self.nof_lits + 1):
            self.sign(j)
        for j in range(1, self.nof_lits + 1):
            self.leaf(j)

        enc = CNF()

        # exactly one feature per node (including class/label)
        for j in range(1, self.nof_lits + 1):
            feats = [self.feat(j, r) for r in range(1, self.nof_feats + 2)]
            one = CardEnc.equals(lits=feats, vpool=self.idpool, encoding=self.options.enc)
            enc.extend(one)

        # at most one class/label per node
        for j in range(1, self.nof_lits + 1):
            labels = [self.label(j, z) for z in self.labels]
            am1 = CardEnc.atmost(lits=labels, vpool=self.idpool, encoding=self.options.enc)
            enc.extend(am1)

        # leaf constraints
        enc.append([-self.leaf(1)            ])  # first node can't be a leaf
        enc.append([ self.leaf(self.nof_lits)])  # last node should be a leaf

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
        for i in range(self.nof_samps):
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

    def add_bsymm(self, enc):
        """
            Symmetry breaking constraints.
        """

        # features in all nodes are sorted
        for j in range(1, self.nof_lits):
            for r1 in range(1, self.nof_feats + 1):
                following = [self.feat(j + 1, r2) for r2 in range(r1 + 1, self.nof_feats + 2)]
                enc.append([self.leaf(j), -self.feat(j, r1)] + following)

        # first features in all rules are sorted
        enc.append([self.leaf(0)])
        for j1, j2 in itertools.combinations(range(1, self.nof_lits + 1), 2):
            for r1 in range(1, self.nof_feats + 1):
                following = [self.feat(j2, r2) for r2 in range(r1, self.nof_feats + 2)]
                enc.append([-self.leaf(j1 - 1), -self.leaf(j2 - 1), -self.feat(j1, r1)] + following)

    def feat(self, j, r):
        """
            True if literal at node j decides on feature r.
        """

        return self.idpool.id('feat_{0}_{1}'.format(j, r))

    def sign(self, j):
        """
            True if literal at node j is positive.
        """

        return self.idpool.id('sign_{0}'.format(j))

    def leaf(self, j):
        """
            True if node j is a leaf.
        """

        return self.feat(j, self.nof_feats + 1)

    def label(self, j, z):
        """
            True if literal at node j represents class = z.
        """

        return self.idpool.id('label_{0}_{1}'.format(j, z))

    def sets0(self, j, r):
        """
            Node j set feature r to 0.
        """

        return self.idpool.id('sets0_{0}_{1}'.format(j, r))

    def sets1(self, j, r):
        """
            Node j set feature r to 1.
        """

        return self.idpool.id('sets1_{0}_{1}'.format(j, r))

    def agree(self, j, i, r=None):
        """
            True iff node j agrees with sample i on feature r.
        """

        if r != None:
            return self.idpool.id('agree_{0}_{1}_{2}'.format(j, i, r))
        else:
            return self.idpool.id('agree_{0}_{1}'.format(j, i))

    def reached(self, j, i):
        """
            True id node j accepts example i.
        """

        return self.idpool.id('reached_{0}_{1}'.format(j, i))

    def covered(self, j, i):
        """
            True id item i is covered by leaf j.
        """

        return self.idpool.id('covered_{0}_{1}'.format(j, i))

    def extract_cover(self, model):
        """
            Extracts a resulting DS from a model returned by a SAT oracle.
        """

        premise = []

        for j in range(1, self.nof_lits + 1):
            for r in range(1, self.nof_feats + 2):
                if model[self.feat(j, r)] > 0:
                    if model[self.leaf(j)] > 0:
                        for lb in self.labels:
                            if model[self.label(j, lb)] > 0:
                                label = lb
                                break

                        # creating the rule
                        rule = Rule(fvars=premise, label=label,
                                mapping=self.data.fvmap)

                        self.covrs[label].append(rule)
                        self.cost += len(rule)

                        if self.options.verb:
                            print('c1 cover:', str(rule))

                        premise = []
                    else:
                        id_orig = self.ffmap.opp[r - 1]

                        if model[self.sign(j)] * id_orig > 0:
                            premise.append(id_orig)
                        else:
                            premise.append(-id_orig)

        return self.covrs
