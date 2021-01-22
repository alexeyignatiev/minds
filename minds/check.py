#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## check.py
##
##  Created on: Dec 3, 2017
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from __future__ import print_function
import copy
import itertools
from pysat.card import *
from pysat.examples.rc2 import RC2, RC2Stratified
from pysat.formula import WCNF
from pysat.solvers import Solver
import resource


#
#==============================================================================
class ConsistencyChecker(object):
    """
        IHS MaxSAT-based consistency checker.
    """

    def __init__(self, data, options):
        """
            Constructor.
        """

        self.status = True if len(data.feats[-1]) > 1 else False
        if not self.status:
            return

        self.init_time = resource.getrusage(resource.RUSAGE_SELF).ru_utime

        self.data = data
        self.dbin = copy.deepcopy(data)  # samples to binarize
        self.options = options

        # binarizing the data properly
        for i in range(len(self.data.samps)):
            samp_bin = self.data.samps[i][:-1]
            for l in samp_bin:
                if l > 0:  # negative literal means that the feature is binary
                    name, lit = self.data.fvmap.opp[l]
                    j = self.data.nm2id[name]

                    if len(self.data.feats[j]) > 2:
                        samp_bin += [-self.data.fvmap.dir[(name, l)] for l in sorted(self.data.feats[j].difference(set([lit])))]

            self.dbin.samps[i] = samp_bin

        # clusterizing samples
        self.clust = {self.data.fvmap.dir[(self.data.names[-1], v)]: [] for v in self.data.feats[-1]}
        for i, s in enumerate(self.data.samps):
            self.clust[s[-1]].append(i)

        # creating a formula
        self.formula = WCNF()
        self.formula.nv = len(data.samps)
        self.formula.topw = len(data.samps) + 1

        # soft clauses and their weights
        for i, sample in enumerate(data.samps):
            self.formula.soft.append([i + 1])
            self.formula.wght.append(data.wghts[i])

        # hard clauses (pairwise overlapping samples)
        for c1, c2 in itertools.combinations(self.clust.keys(), 2):
            for i in self.clust[c1]:
                samp = set([-l for l in self.dbin.samps[i]])

                for j in self.clust[c2]:
                    if not samp.intersection(set(self.dbin.samps[j])):
                        # these two samples do not clash!
                        self.formula.hard.append([-i - 1, -j - 1])

    def do(self):
        """
            Call a MaxSAT solver.
        """

        # deciding whether or not to stratify
        if max(self.formula.wght) > min(self.formula.wght):
            MXS = RC2Stratified
        else:
            MXS = RC2

        # here we use MSE18 configuration 'b'
        with MXS(self.formula, solver='g3' if self.options.solver in ('cd', 'cdl', 'cadical') else self.options.solver, adapt=True,
                exhaust=True, incr=False, minz=True, trim=0, verbose=0) as rc2:
            rc2.compute()

            model = rc2.model[:]
            self.consistent = list(map(lambda l: l - 1, filter(lambda l: 0 < l <= self.formula.nv, model)))

        # decide whether or not we keep all samples
        if len(self.consistent) == len(self.data.samps):
            return True
        else:
            return False

    def remove_inconsistent(self):
        """
            Take a smallest subset of all inconsistent samples out.
        """

        samps = [self.data.samps[i] for i in self.consistent]
        wghts = [self.data.wghts[i] for i in self.consistent]

        self.data.samps_filt = len(self.data.samps) - len(samps)
        self.data.wghts_filt = sum(self.data.wghts) - sum(wghts)

        self.data.samps = samps
        self.data.wghts = wghts

        # recomputing the number of classes
        classes = set([])
        for sample in self.data.samps:
            classes.add(sample[-1])

        # removing variables for unnecessary classes
        self.data.deleted = set([])
        deleted_vars = set([])
        for l in self.data.feats[-1]:
            pair = (self.data.names[-1], l)
            var = self.data.fvmap.dir[pair]

            if var not in classes:
                del(self.data.fvmap.dir[pair])
                del(self.data.fvmap.opp[var])
                self.data.deleted.add(l)
                deleted_vars.add(var)

        self.data.feats[-1] = list(filter(lambda x: x not in self.data.deleted, self.data.feats[-1]))
        self.data.deleted = deleted_vars

        # updating status
        self.status = True if len(classes) > 1 else False

        self.time = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_time
        self.time += resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime

    def dump_consistent(self):
        """
            Dump the largest consistent subset of samples to a file.
        """

        fname = '{0}-consistent.csv'.format(os.path.splitext(self.options.files[0])[0])

        with open(fname, 'w') as fp:
            print(','.join(self.data.names), file=fp)

            for s, w in zip(self.data.samps, self.data.wghts):
                feats = ['' for n in xrange(len(self.data.names))]

                for l in s:
                    name, val = self.data.fvmap.opp[l]
                    feats[self.data.nm2id[name]] = val

                for i in xrange(w):
                    print(','.join(feats), file=fp)

