#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## dscheck.py
##
##  Created on: Jan 10, 2018
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from __future__ import print_function
import collections
import getopt
import gzip
import os
import sys
import six
from six.moves import range


#
#==============================================================================
class Data(object):
    """
        A class for simplifying a (training) data set.
    """

    def __init__(self, from_fp=None, separator=None):
        """
            Constructor.
        """

        self.names = None
        self.feats = None
        self.samps = None
        self.wghts = None

        if from_fp:
            self.from_fp(fp=from_fp, separator=separator)

    def from_fp(self, fp=None, separator=','):
        """
            Get data from a CSV file.
        """

        if fp:
            lines = fp.readlines()

            # reading preamble
            self.names = [w.strip() for w in lines[0].strip().split(separator)]
            self.feats = [set([]) for n in self.names]
            del(lines[0])

            # filling name to id mapping
            self.nm2id = {name: i for i, name in enumerate(self.names)}

            # reading training samples
            self.samps, self.wghts, self.classes = [], [], {}

            for line, w in six.iteritems(collections.Counter(lines)):
                sample = [word.strip() for word in line.strip().split(separator)]

                for i, f in enumerate(sample):
                    if f:
                        self.feats[i].add(f)

                self.samps.append(sample)
                self.wghts.append(w)

                # clasterizing the samples
                if sample[-1] not in self.classes:
                    self.classes[sample[-1]] = []

                self.classes[sample[-1]].append(len(self.samps) - 1)

    def check_ds(self, dset, check_overlap, verb):
        """
            Check if the decision set covers the data correctly.
            Every rule should cover at least one sample of the
            same class and do not cover any sample of other classes.
        """

        def equals(sample_val, val):
            if val[0] == '(' and val[-1] in (')', ']') and ' .. ' in val:
                # the value is an interval
                min_, max_ = val.strip('()]').split(' .. ')

                v = float(sample_val)
                lb_ok = True if min_ == '-inf' else v > float(min_)
                ub_ok = True if max_ == 'inf' else v <= float(max_)
                return lb_ok and ub_ok
            else:
                return sample_val == val

        covered = set([])
        overlap = set([])  # samples exhibiting overlap

        for rule in dset.rules:
            label = rule[-1]

            assert label[0] == self.names[-1], 'Wrong label name in the decision set:'.format(label[0])
            assert label[1] in self.feats[-1], 'Wrong label value in the decision set: {0}'.format(label[1])

            # checking same class
            for sid in self.classes[label[1]]:
                if sid in covered:
                    continue

                sample = self.samps[sid]

                for r in rule[:-1]:
                    name, val, pos = r
                    id_ = self.nm2id[name]

                    if sample[id_] == '' or (pos == True and not equals(sample[id_], val)) or (pos == False and equals(sample[id_], val)):
                        break  # does not cover
                else:
                    covered.add(sid)

            # checking other classes (overlap)
            if check_overlap:
                others = set(six.iterkeys(self.classes)).difference(set([label[1]]))
                for lb in others:
                    for sid in self.classes[lb]:
                        sample = self.samps[sid]

                        for r in rule[:-1]:
                            name, val, pos = r
                            id_ = self.nm2id[name]

                            if sample[id_] == '' or (pos == True and not equals(sample[id_], val)) or (pos == False and equals(sample[id_], val)):
                                break  # does not cover
                        else:
                            overlap.add(sid)

        # trying the default rule
        if dset.default:
            for sid in self.classes[dset.default[1]]:
                if sid not in covered:
                    covered.add(sid)

        if verb and len(covered) != len(self.samps):
            print('not covered:')

            for sid in set(range(len(self.samps))).difference(covered):
                self.dump_sample(sid)

        if verb and overlap:
            print('overlap:')

            for sid in overlap:
                self.dump_sample(sid)

        if len(covered) != len(self.samps) or overlap:
            allsamps = set(range(len(self.samps)))
            uncovered = allsamps.difference(covered)
            failures = uncovered.union(overlap)
            noffails = sum([self.wghts[sid] for sid in list(failures)])
            print('accuracy: {0:.2f}%'.format((100.0 * (sum(self.wghts) - noffails)) / sum(self.wghts)))

    def dump_sample(self, sid, fp=sys.stdout):
        """
            Dump the resulting dataset to a file.
        """

        if fp:
            sample = ','.join(self.samps[sid])

            for i in range(self.wghts[sid]):
                print(sample, file=fp)


#
#==============================================================================
class DSet(object):
    """
        Class for storing a resulting decision set.
    """

    def __init__(self, from_fp=None):
        """
            Constructor.
        """

        self.rules = []
        self.default = None

        if from_fp:
            self.parse(from_fp)
        else:
            assert 0, 'No decision set file given'

    def parse(self, fp):
        """
            Parsing procedure.
        """

        lines = fp.readlines()
        lines = filter(lambda x: 'cover:' in x, lines)
        lines = map(lambda x: x.split(':', 1)[1].strip(), lines)

        for line in lines:
            body, label = line.split(' => ')
            label = label.strip('\'').split(': ')

            if body == 'true':
                assert self.default == None, 'At most one default rule is allowed'

                if verb:
                    print('default rule is detected - the \'else\' semantics is used')

                self.default = label
                continue

            rule = []

            for l in body.split(', '):
                if l[0] == '\'':
                    name, val = l.strip('\'').rsplit(': ', 1)
                    lnew = tuple([name, val, True])
                elif l[0] == 'n':  # negative literal
                    name, val = l[4:].strip('\'').rsplit(': ', 1)
                    lnew = tuple([name, val, False])

                # # handling intervals
                # if '..' in val:
                #     lb, ub = [float(v) for v in val[1:-1].split(' .. ')]
                #     lb = tuple([lb, True]) if val[ 0] == '(' else tuple([lb, False])
                #     ub = tuple([ub, True]) if val[-1] == ')' else tuple([ub, False])

                #     lnew = list(lnew)
                #     lnew[1] = tuple([lb, ub])
                #     lnew = tuple(lnew)

                rule.append(lnew)
            rule.append(tuple(label + [True]))

            self.rules.append(rule)

        print('# rules:', len(self.rules) + int(self.default != None))
        print('# lits:', sum([len(r) for r in self.rules]) + int(self.default != None))


#
#==============================================================================
def parse_options():
    """
        Parses command-line options.
    """

    try:
        opts, args = getopt.getopt(sys.argv[1:],
                                   'd:hos:v',
                                   ['dset=',
                                    'help',
                                    'overlap',
                                    'sep=',
                                    'verbose'])
    except getopt.GetoptError as err:
        sys.stderr.write(str(err).capitalize() + '\n')
        usage()
        sys.exit(1)

    dset = None
    overlap = False
    sep = ','
    verb = False

    for opt, arg in opts:
        if opt in ('-d', '--dset'):
            dset = str(arg)
        elif opt in ('-h', '--help'):
            usage()
            sys.exit(0)
        elif opt in ('-o', '--overlap'):
            overlap = True
        elif opt in ('-s', '--sep'):
            sep = str(arg)
        elif opt in ('-v', '--verbose'):
            verb = True
        else:
            assert False, 'Unhandled option: {0} {1}'.format(opt, arg)

    return dset, overlap, sep, verb, args


#
#==============================================================================
def usage():
    """
        Prints help message.
    """

    print('Usage:', os.path.basename(sys.argv[0]), '[options] file')
    print('Options:')
    print('        -d, --dset=<string>    File where an optimal decision set is stored (default = none)')
    print('        -h, --help')
    print('        -o, --overlap          Test for overlap (i.e. if more than 1 class is assigned to a sample)')
    print('        -s, --sep=<string>     Separator used in the input CSV file (default = \',\')')
    print('        -v, --verbose          Be verbose')


#
#==============================================================================
if __name__ == '__main__':
    dset, overlap, sep, verb, files = parse_options()

    if files:
        if files[0].endswith('.gz'):
            with gzip.open(files[0], 'rt') as fp:
                data = Data(from_fp=fp, separator=sep)
        else:
            with open(files[0]) as fp:
                data = Data(from_fp=fp, separator=sep)

        if dset:
            with open(dset, 'r') as fp:
                dset = DSet(from_fp=fp)
        else:
            dset = DSet(from_fp=sys.stdin)

        data.check_ds(dset, overlap, verb)
