#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## data.py
##
##  Created on: Sep 20, 2017
##      Author: Alexey S. Ignatiev
##      E-mail: aignatiev@ciencias.ulisboa.pt
##

#
#==============================================================================
from __future__ import print_function
import collections
import itertools
import os
import pandas
import six

# a dirty hack (xrange does not exist in Python3)
#==============================================================================
try:
    xrange
except NameError:
    xrange = range


#
#==============================================================================
class Data(object):
    """
        Class for representing data (transactions).
    """

    def __init__(self, filename=None, fpointer=None, mapfile=None,
            separator=' ', ranges=None):
        """
            Constructor and parser.
        """

        self.names = None
        self.nm2id = None
        self.samps = None
        self.wghts = None
        self.feats = None
        self.fvmap = None
        self.ovmap = {}
        self.vimap = {}
        self.fvars = None
        self.fname = filename
        self.mname = mapfile
        self.deleted = set([])

        if ranges:
            self.intvs = [i / float(ranges) for i in xrange(1, ranges)]
        else:
            self.intvs = None

        if filename:
            with open(filename, 'r') as fp:
                self.parse(fp, separator)
        elif fpointer:
            self.parse(fpointer, separator)

        if self.mname:
            self.read_orig_values()

    def parse(self, fp, separator):
        """
            Parse input file.
        """

        # reading data set from file
        lines = fp.readlines()

        # reading preamble
        self.names = lines[0].strip().split(separator)
        self.feats = [set([]) for n in self.names]
        del(lines[0])

        # filling name to id mapping
        self.nm2id = {name: i for i, name in enumerate(self.names)}

        # reading training samples
        self.samps, self.wghts = [], []

        for line, w in six.iteritems(collections.Counter(lines)):
            sample = line.strip().split(separator)
            for i, f in enumerate(sample):
                if f:
                    self.feats[i].add(f)
            self.samps.append(sample)
            self.wghts.append(w)

        # direct and opposite mappings for items
        idpool = itertools.count(start=1)
        FVMap = collections.namedtuple('FVMap', ['dir', 'opp'])
        self.fvmap = FVMap(dir={}, opp={})

        # mapping features to ids
        for i in xrange(len(self.names) - 1):
            feats = list(self.feats[i])

            # try to rangify this feature
            if self.intvs and len(feats) > len(self.intvs) + 1:
                feats = self.rangify(feats, i)
                self.feats[i] = set(feats)

            if len(feats) != 2:
                for l in feats:
                    self.fvmap.dir[(self.names[i], l)] = next(idpool)
            else:
                var = next(idpool)
                self.fvmap.dir[(self.names[i], feats[0])] = var
                self.fvmap.dir[(self.names[i], feats[1])] = -var

        # use ranges for updating samples
        if self.vimap:
            for i, s in enumerate(self.samps):
                self.samps[i] = [self.vimap[j][v] if j in self.vimap else v for j, v in enumerate(s)]

            # recomputing the weights
            counter = collections.Counter()
            for s, w in zip(self.samps, self.wghts):
                counter[tuple(s)] += w

            self.samps = []
            self.wghts = []
            for s, w in six.iteritems(counter):
                self.samps.append(list(s))
                self.wghts.append(w)

        # all labels are marked with distinct ids
        for l in self.feats[-1]:
            self.fvmap.dir[(self.names[-1], l)] = next(idpool)

        # opposite mapping
        for key, val in six.iteritems(self.fvmap.dir):
            self.fvmap.opp[val] = key

        # encoding samples
        for i in xrange(len(self.samps)):
            self.samps[i] = [self.fvmap.dir[(self.names[j], self.samps[i][j])] for j in xrange(len(self.samps[i])) if self.samps[i][j]]

        # determining feature variables (excluding class variables)
        for v, pair in six.iteritems(self.fvmap.opp):
            if pair[0] == self.names[-1]:
                self.fvars = v - 1
                break

    def read_orig_values(self):
        """
            Read original values for all the features.
            (from a separate CSV file)
        """

        self.ovmap = {}

        for line in open(self.mname, 'r'):
            featval, bits = line.strip().split(',')
            feat, val = featval.split(':')

            for i, b in enumerate(bits):
                f = '{0}:b{1}'.format(feat, i + 1)
                v = self.fvmap.dir[(f, '1')]

                if v not in self.ovmap:
                    self.ovmap[v] = [feat]

                if -v not in self.ovmap:
                    self.ovmap[-v] = [feat]

                self.ovmap[v if b == '1' else -v].append(val)

    def dump_result(self, primes, covers):
        """
            Save result to a CSV file.
        """

        fname = '{0}-result.csv'.format(os.path.splitext(self.fname)[0])

        for f in self.feats:
            if len(f) > 2:
                print('c2 non-binary features detected; not dumping the result')
                return

        with open(fname, 'w') as fp:
            print(','.join(self.names), file=fp)

            for cid in covers:
                for pid in covers[cid]:
                    feats = ['' for n in xrange(len(self.names))]

                    for l in primes[cid][pid - 1]:
                        name, val = self.fvmap.opp[l]
                        feats[self.nm2id[name]] = val

                    # label
                    name, val = self.fvmap.opp[cid]
                    feats[self.nm2id[name]] = val

                    print(','.join(feats), file=fp)

    def rangify(self, valset, feature_id):
        """
            Try to create a given number of intervals instead of unique
            feature values.
        """

        def isnumber(val):
            try:
                f = float(val)  # integer can also be treated as float
                return f
            except ValueError:
                return None

        vals = {}

        for v in valset:
            f = isnumber(v)
            if f != None:
                vals[v] = f
            else:
                break
        else:
            # all values are numeric
            # divide them into intervals
            self.vimap[feature_id] = {}

            # creating value thresholds
            thresholds = pandas.Series(vals.values()).quantile(self.intvs).unique()

            # creating intervals
            intvs = []
            for i, t in enumerate(thresholds):
                intvs.append('({0} .. {1}]'.format('-inf' if i == 0 else thresholds[i - 1], t))
            intvs.append('({0} .. +inf)'.format(thresholds[-1]))

            for v in vals:
                for i, t in enumerate(thresholds):
                    if vals[v] <= t:
                        self.vimap[feature_id][v] = intvs[i]
                        break
                else:
                    self.vimap[feature_id][v] = intvs[-1]

            return intvs

        # there are some non-numeric values; do nothing
        return valset
