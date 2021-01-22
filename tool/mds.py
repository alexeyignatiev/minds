#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## mds.py
##
##  Created on: Dec 3, 2017
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

# print function as in Python3
#==============================================================================
from __future__ import print_function
from minds.check import ConsistencyChecker
from minds.data import Data
from minds.minds1 import MinDS1Rules
from minds.mp92 import MP92Rules
from minds.options import Options
from minds.mxsatl import MaxSATLits
from minds.mxsatls import MaxSATLitsSep
from minds.mxsatsp import MaxSATSparse
from minds.satr import SATRules
from minds.satl import SATLits
from minds.satls import SATLitsSep
from minds.twostage import TwoStageApproach
import os
import resource
import six
import sys


#
#==============================================================================
def show_info():
    """
        Print info message.
    """

    print('c MDS: miner of (optimal) decision sets')
    print('c author: Alexey Ignatiev [email:alexey.ignatiev@monash.edu]')
    print('')


#
#==============================================================================
def do_two_stage(data, options):
    """
        Run the prime-based approach.
    """

    ruler = TwoStageApproach(data, options)
    covers = ruler.compute()

    # save result to a CSV file
    if options.rdump:
        data.dump_result(primes, covers)


#
#==============================================================================
def do_single_stage(data, options):
    """
        Run a single-stage SAT-based approach.
    """

    if options.approach == 'mp92':
        solver = MP92Rules(data, options)  # MP92 approach
    elif options.approach in ('satr', 'sr'):
        solver = SATRules(data, options)  # MinDS2 and MinDS2*
    elif options.approach in ('satl', 'sl'):
        solver = SATLits(data, options)  # Opt
    elif options.approach in ('satls', 'sls'):
        solver = SATLitsSep(data, options)  # OptSep
    elif options.approach in ('mxsatls', 'mls'):
        solver = MaxSATLitsSep(data, options)  # MOptSep
    elif options.approach in ('mxsatsparse', 'msparse', 'sparse'):
        solver = MaxSATSparse(data, options)  # Sparse
    elif options.approach in ('mxsatl', 'ml'):
        solver = MaxSATLits(data, options)  # MOpt
    else:
        solver = MinDS1Rules(data, options)  # MinDS1

    covers = solver.compute()

    # dealing with default rules (if any)
    if options.verb:
        wghts, label = [], None
        if options.default:
            # if the 'default' option is given
            for lb in six.iterkeys(covers):
                wghts.append(tuple([lb, sum(data.wghts[i] for i in solver.samps[lb])]))
            label = max(wghts, key=lambda p: p[1])[0]
        else:
            # for the sparse model only:
            # checking if there are default rules
            # and selecting the best among them
            for lb, premise in six.iteritems(covers):
                if len(premise) == 1 and len(premise[0]) == 0:
                    wghts.append(tuple([lb, sum(data.wghts[i] for i in solver.samps[lb])]))

            if wghts:
                label = max(filter(lambda p: len(covers[p[0]]) != 1 or covers[p[0]] != [], wghts), key=lambda p: p[1])[0]

        if label is not None:
            print('c1 cover: true => {0}'.format(': '.join(data.fvmap.opp[label])))

    print('c2 cover size: {0}'.format(sum([len(p) for p in six.itervalues(covers)])))
    print('c2 cover wght: {0}'.format(solver.cost))

    if hasattr(solver, 'accy'):
        print('c2 accy filtr: {0:.2f}%'.format(solver.accy))
    if hasattr(solver, 'accy_tot'):
        print('c2 accy total: {0:.2f}%'.format(solver.accy_tot))

    print('c2 cover time: {0:.4f}'.format(solver.time))


#
#==============================================================================
if __name__ == '__main__':
    # parsing command-line options
    options = Options(sys.argv)

    # showing head
    show_info()

    # parsing data
    if options.files:
        data = Data(filename=options.files[0], mapfile=options.mapfile,
                separator=options.separator, ranges=options.ranges)
    else:
        data = Data(fpointer=sys.stdin, mapfile=options.mapfile,
                separator=options.separator)

    if options.verb:
        print('c0 # of samps: {0} ({1} weighted)'.format(sum(data.wghts), len(data.samps)))
        print('c0 # of feats: {0} ({1} binary)'.format(len(data.names) - 1, len(list(filter(lambda x: x > 0, data.fvmap.opp.keys()))) - len(data.feats[-1])))
        print('c0 # of labls: {0}'.format(len(data.feats[-1])))

        used_time = resource.getrusage(resource.RUSAGE_SELF).ru_utime
        print('c0 parse time: {0:.4f}'.format(used_time))
        print('')

    if options.noccheck == False:
        # phase0: consistency check
        checker = ConsistencyChecker(data, options)
        if checker.status and checker.do() == False:
            checker.remove_inconsistent()
            if options.verb:
                print('c0 data set is inconsistent')
                print('c0 filtering out {0} samples ({1} left)'.format(data.samps_filt, len(data.samps)))
                print('c0 filtering out {0} weights ({1} left)'.format(data.wghts_filt, sum(data.wghts)))
                print('c0 check time: {0:.4f}'.format(checker.time))
                print('')

            if options.cdump:
                checker.dump_consistent()

        if checker.status == False:
            print('c0 not enough classes => classification makes no sense')
            sys.exit(1)

    if options.approach in ('2', '2stage', 'pbased'):
        do_two_stage(data, options)
    else:  # single-phase models (sat, mp92, minds1, opt, etc)
        do_single_stage(data, options)

    if options.verb:
        total_time = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_utime
        print('c3 total time: {0:.4f}'.format(total_time))
