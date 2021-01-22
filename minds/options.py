#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## options.py
##
##  Created on: Sep 20, 2017
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from __future__ import print_function
import decimal
import getopt
import math
import os
from pysat.card import EncType
import sys

#
#==============================================================================
encmap = {
    "pw": EncType.pairwise,
    "seqc": EncType.seqcounter,
    "cardn": EncType.cardnetwrk,
    "sortn": EncType.sortnetwrk,
    "tot": EncType.totalizer,
    "mtot": EncType.mtotalizer,
    "kmtot": EncType.kmtotalizer,
    "native": EncType.native
}


#
#==============================================================================
class Options(object):
    """
        Class for representing command-line options.
    """

    def __init__(self, command=None):
        """
            Constructor.
        """

        self.accuracy = 100.0
        self.am1 = False
        self.approach = '2stage'
        self.approx = 0
        self.blo = False
        self.bsymm = False
        self.to_compute = 'all'
        self.default = False
        self.enc = 'cardn'
        self.exhaust = False
        self.files = None
        self.solver = 'm22'
        self.primer = 'sorted'
        self.cover = 'mxsat'
        self.lambda_ = '0.005'
        self.lambda_adaptive = False
        self.mapfile = None
        self.mcmd = ''
        self.minz = False
        self.noneg = False
        self.opt = False
        self.plimit = 0
        self.noccheck = False
        self.cdump = False
        self.pdump = False
        self.rdump = False
        self.ranges = 0
        self.separator = ','
        self.trim = 0
        self.use_cld = False
        self.update = 0
        self.verb = 0
        self.weighted = False

        if command:
            self.parse(command)

    def parse(self, command):
        """
            Parser.
        """

        self.command = command

        try:
            opts, args = getopt.getopt(command[1:],
                                    '1a:bBc:C:de:hl:mnp:r:s:t:u:vwx',
                                    ['accy=',
                                        'am1',
                                        'approach=',
                                        'approx=',
                                        'blo',
                                        'bsymm',
                                        'class=',
                                        'cdump',
                                        'cover=',
                                        'default',
                                        'do-cld',
                                        'enc=',
                                        'exhaust'
                                        'help',
                                        'lambda=',
                                        'lambda-adapt',
                                        'map-file=',
                                        'mcmd=',
                                        'minz',
                                        'no-neg',
                                        'no-ccheck',
                                        'opt',
                                        'pdump',
                                        'rdump',
                                        'plimit=',
                                        'primer=',
                                        'ranges=',
                                        'sep=',
                                        'solver=',
                                        'trim=',
                                        'update=',
                                        'verbose',
                                        'weighted'])
        except getopt.GetoptError as err:
            sys.stderr.write(str(err).capitalize() + '\n')
            self.usage()
            sys.exit(1)

        for opt, arg in opts:
            if opt == '--accy':
                self.accuracy = float(arg)
            elif opt in ('-1', '--am1'):
                self.am1 = True
            elif opt in ('-a', '--approach'):
                self.approach = str(arg)
            elif opt == '--approx':
                self.approx = int(arg)
            elif opt in ('-b', '--blo'):
                self.blo = True
            elif opt in ('-B', '--bsymm'):
                self.bsymm = True
            elif opt in ('-c', '--class'):
                self.to_compute = str(arg)
            elif opt in ('-C', '--cover'):
                self.cover = str(arg)
            elif opt == '--cdump':
                self.cdump = True
            elif opt == '--default':
                self.default = True
            elif opt in ('-d', '--do-cld'):
                self.use_cld = True
            elif opt in ('-e', '--enc'):
                self.enc = str(arg)
            elif opt in ('-h', '--help'):
                self.usage()
                sys.exit(0)
            elif opt in ('-l', '--plimit'):
                self.plimit = int(arg)
                if self.plimit == 'best':
                    self.plimit = -1
                else:
                    self.plimit = int(self.plimit)
            elif opt == '--lambda':
                self.lambda_ = str(arg)
            elif opt == '--lambda-adapt':
                self.lambda_adaptive = True
            elif opt == '--map-file':
                self.mapfile = str(arg)
            elif opt == '--mcmd':
                self.mcmd = str(arg)
            elif opt in ('-m', '--minz'):
                self.minz = True
            elif opt in ('-n', '--no-neg'):
                self.noneg = True
            elif opt == '--no-ccheck':
                self.noccheck = True
            elif opt == '--opt':
                self.opt = True
            elif opt in ('-p', '--primer'):
                self.primer = str(arg)
            elif opt == '--pdump':
                self.pdump = True
            elif opt in ('-r', '--ranges'):
                self.ranges = int(arg)
            elif opt == '--rdump':
                self.rdump = True
            elif opt == '--sep':
                self.separator = str(arg)
            elif opt in ('-s', '--solver'):
                self.solver = str(arg)
            elif opt in ('-t', '--trim'):
                self.trim = int(arg)
            elif opt in ('-u', '--update'):
                self.update = int(arg)
            elif opt in ('-v', '--verbose'):
                self.verb += 1
            elif opt in ('-w', '--weighted'):
                self.weighted = True
            elif opt in ('-x', '--exhaust'):
                self.exhaust = True
            else:
                assert False, 'Unhandled option: {0} {1}'.format(opt, arg)

        self.enc = encmap[self.enc]
        self.files = args

    def usage(self):
        """
            Print usage message.
        """

        print('Usage: ' + os.path.basename(self.command[0]) + ' [options] training-data')
        print('Options:')
        print('        -1, --am1                  Detect AtMost1 constraints in RC2')
        print('        --accy=<float>             Target at least this accuracy')
        print('                                   Available values: [0.0 .. 100.0] (default = 100.0)')
        print('        -a, --approach=<string>    Approach to use')
        print('                                   Available values: mxsatl, mxsatls, sparse, minds1, mp92, satr, satl, satls (default = 2stage)')
        print('        --approx=<int>             Approximate set cover with at most k attempts')
        print('                                   Available values: [0 .. INT_MAX] (default = 0)')
        print('        -b, --blo                  Apply BLO when solving MaxSAT')
        print('        -B, --bsymm                Use symmetry breaking constraints in SAT-based approaches')
        print('        -c, --class=<string>       Class to compute')
        print('                                   Available values: all, best, any-specific-label (default = all)')
        print('                                   Note: if more than one class is chosen and the approach is sat/mp92/minds1,')
        print('                                         the tool pretends that other classes do not exist')
        print('        --cdump                    Dump largest consistent subset of input samples')
        print('        -C, --cover=<string>       Approach to apply for computing a prime cover')
        print('                                   Available values: mxsat, cplex, gurobi (default = mxsat)')
        print('        -d, --do-cld               Do D clause calls')
        print('        --default                  Print default rule')
        print('        -e, --enc=<string>         Encoding to use')
        print('                                   Available values: cardn, kmtot, mtot, sortn, tot (default = cardn)')
        print('        -h, --help')
        print('        -l, --plimit=<int>         Compute at most this number of primes per sample')
        print('                                   Available values: [0 .. INT_MAX] (default: 0)')
        print('        --lambda=<float>           Parameter lambda used in the sparse model')
        print('                                   Available values: [0, FLOAT_MAX], 0.005')
        print('        --lambda-adapt             Use adaptive lambda used in the sparse model')
        print('        --map-file=<string>        Path to a file containing a mapping to original feature values. (default: none)')
        print('        --mcmd=<string>            Command to run a MaxSAT solver')
        print('        -m, --minz                 Use unsatisfiable core heuristic minimization in RC2')
        print('        --no-ccheck                Do not perform consistency check')
        print('        -p, --primer=<string>      Prime implicant enumerator to use')
        print('                                   Available values: lbx, mcsls, sorted (default = sorted)')
        print('        --pdump                    Dump MaxSAT formula for enumerating primes')
        print('                                   (makes sense only when using an MCS-based primer)')
        print('        -r, --ranges=<int>         Try to cluster numeric features values into this number of ranges')
        print('                                   Available values: [0 .. INT_MAX] (default = 0)')
        print('        --rdump                    Dump resulting CSV table')
        print('        --sep=<string>             Field separator used in input file (default = \',\')')
        print('        -s, --solver=<string>      SAT solver to use')
        print('                                   Available values: g3, lgl, m22, mc, mgh (default = m22)')
        print('        -t, --trim=<int>           Trim unsatisfiable core at most this number of times')
        print('                                   Available values: [0 .. INT_MAX] (default = 0)')
        print('        -u, --update=<int>         Update dual solutions every k iterations')
        print('                                   Available values: [0 .. INT_MAX] (default = 1)')
        print('        -v, --verbose              Be more verbose')
        print('        -w, --weighted             Minimize the total number of literals')
        print('        -x, --exhaust              Do unsatisfiable core exhaustion in RC2')
