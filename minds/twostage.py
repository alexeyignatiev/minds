#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## twostage.py
##
##  Created on: Nov 27, 2020
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
import collections
from minds.cover import Coverer
from minds.ruler import Ruler
import os
import resource
import socket
import six


#
#==============================================================================
class TwoStageApproach(object):
    """
        Individual rule-based decision set miner.
    """

    def __init__(self, data, options):
        """
            Constructor.
        """

        # saving data
        self.data = data

        # samples clustered by their label
        self.clusters = collections.defaultdict(lambda: [])

        # binarizing the data properly
        for i in range(len(self.data.samps)):
            samp_bin, out = self.data.samps[i][:-1], self.data.samps[i][-1]
            for l in samp_bin:
                if l > 0:  # negative literal means that the feature is binary
                    name, lit = self.data.fvmap.opp[l]
                    j = self.data.nm2id[name]

                    if len(self.data.feats[j]) > 2:
                        samp_bin += [-self.data.fvmap.dir[(name, l)] for l in sorted(self.data.feats[j].difference(set([lit])))]

            self.data.samps[i] = samp_bin + [out]
            self.clusters[out].append(i)

        # saving options
        self.options = options

        # depending on this option, we compute either one class or all of them
        if self.options.to_compute == 'all':
            self.labels = [self.data.fvmap.dir[self.data.names[-1], c] for c in sorted(self.data.feats[-1])]
        elif self.options.to_compute == 'best':
            raise NotImplementedError('Best class computation is not supported')
        else:
            to_compute = self.options.to_compute.split(',')
            self.labels = [self.data.fvmap.dir[self.data.names[-1], c] for c in to_compute]

        # dictionary storing the rules for all the classes
        self.lcovers = collections.defaultdict(lambda: [])

    def compute(self):
        """
            Compute a decision set with the two-stage approach:
            1. individual rule enumeration
            2. covering the training instances by the rules computed
        """

        nrules, cost = 0, 0

        # going over the labels to compute
        for label in self.labels:

            if self.options.verb:
                print('c0 computing class:', self.data.fvmap.opp[label][1])

            # stage 1
            ruler = Ruler(self.clusters, label, self.data, self.options)
            rules = ruler.enumerate()

            if self.options.verb:
                if self.options.verb > 1:
                    for rule in rules:
                        print('c1 rule:', str(rule))

                print('c1 # of rules: {0}'.format(len(rules)))
                print('c1 rule time: {0:.4f}'.format(ruler.time))
                print('')

            # stage 2
            coverer = Coverer(self.data, self.clusters, rules, label, self.options)
            cover = coverer.compute()

            # some stats
            cost += coverer.cost
            nrules += len(rules)

            # actual cover containing rules
            self.lcovers[label] = [rules[r - 1] for r in cover]

            if self.options.verb:
                for rule in self.lcovers[label]:
                    print('c2 cover:', str(rule))

                print('c2 cover size: {0}'.format(len(self.lcovers[label])))

                if self.options.weighted:
                    print('c2 cover wght: {0}'.format(coverer.cost))

                print('c2 cover time: {0:.4f}'.format(coverer.time))
                print('')

        if self.options.verb:
            print('c3 total rules: {0}'.format(nrules))
            print('c3 total size: {0}'.format(sum(len(cov) for cov in six.itervalues(self.lcovers))))

            if self.options.weighted:
                print('c3 total wght: {0}'.format(cost))

        return self.lcovers
