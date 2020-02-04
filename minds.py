#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## minds.py
##
##  Created on: Dec 3, 2017
##      Author: Alexey S. Ignatiev
##      E-mail: aignatiev@ciencias.ulisboa.pt
##

# print function as in Python3
#==============================================================================
from __future__ import print_function
from check import ConsistencyChecker
from data import Data
from minds1 import MinDS1
from mp92 import MP92
from options import Options
import os
import resource
from sat import SAT
# from smt import SMT
import six
import sys


#
#==============================================================================
def show_info():
    """
        Print info message.
    """

    print('c MinDS: miner of decision sets')
    print('c author(s): Alexey Ignatiev    [email:aignatiev@ciencias.ulisboa.pt]')
    print('c            Joao Marques-Silva [email:jpms@ciencias.ulisboa.pt]')
    print('c            Nina Narodytska    [email:n.narodytska@gmail.com]')
    print('c            Filipe Pereira     [email:filipe.pereira.1995@gmail.com]')
    print('')


#
#==============================================================================
def do_sat_based(data, options):
    """
        Run the SAT-based approach.
    """

    if options.approach == 'mp92':
        solver = MP92(data, options)
    elif options.approach == 'sat':
        solver = SAT(data, options)
    else:
        solver = MinDS1(data, options)

    covers = solver.compute()
    print('c2 cover size: {0}'.format(sum([len(p) for p in six.itervalues(covers)])))
    print('c2 cover wght: {0}'.format(solver.cost))
    print('c2 cover time: {0:.4f}'.format(solver.time))

#
#==============================================================================
if __name__ == '__main__':
    # parsing command-line options
    options = Options(sys.argv)

    # making output unbuffered
    # sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', 0)

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

    # everything else is currently removed
    do_sat_based(data, options)

    if options.verb:
        total_time = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime + resource.getrusage(resource.RUSAGE_SELF).ru_utime
        print('c3 total time: {0:.4f}'.format(total_time))
