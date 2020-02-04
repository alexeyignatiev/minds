#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## options.py
##
##  Created on: Sep 20, 2017
##      Author: Alexey S. Ignatiev
##      E-mail: aignatiev@ciencias.ulisboa.pt
##

#
#==============================================================================
from __future__ import print_function
import getopt
import math
import os
from pysat.card import EncType
from sat import SATMinMode
import sys

#
#==============================================================================
encmap = {
    'pw': EncType.pairwise,
    'seqc': EncType.seqcounter,
    'cardn': EncType.cardnetwrk,
    'sortn': EncType.sortnetwrk,
    'tot': EncType.totalizer,
    'mtot': EncType.mtotalizer,
    'kmtot': EncType.kmtotalizer
}


#
#==============================================================================
class Options(object):
    """
        Class for representing command-line options.
    """

    def __init__(self, command):
        """
            Constructor.
        """

        self.approach = 'sat'
        self.approx = 0
        self.bsymm = False
        self.to_compute = 'all'
        self.enc = 'cardn'
        self.files = None
        self.solver = 'm22'
        self.mapfile = None
        self.mcmd = ''
        self.mode = SATMinMode.rules
        self.opt = False
        self.noccheck = False
        self.cdump = False
        self.pdump = False
        self.rdump = False
        self.ranges = 0
        self.separator = ','
        self.trim = 0
        self.use_cld = False
        self.verb = 0

        if command:
            self.parse(command)

    def parse(self, command):
        """
            Parser.
        """

        self.command = command

        try:
            opts, args = getopt.getopt(command[1:],
                                    'a:c:de:f:hm:nor:s:t:v',
                                    ['approach=',
                                        'approx=',
                                        'bsymm',
                                        'class=',
                                        'cdump',
                                        'do-cld',
                                        'enc=',
                                        'filter=',
                                        'help',
                                        'indprime'
                                        'map-file=',
                                        'mcmd=',
                                        'mode=',
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
                                        'verbose'])
        except getopt.GetoptError as err:
            sys.stderr.write(str(err).capitalize() + '\n')
            self.usage()
            sys.exit(1)

        for opt, arg in opts:
            if opt in ('-a', '--approach'):
                self.approach = str(arg)
            elif opt == '--approx':
                self.approx = int(arg)
            elif opt == '--bsymm':
                self.bsymm = True
            elif opt in ('-c', '--class'):
                self.to_compute = str(arg)
            elif opt == '--cdump':
                self.cdump = True
            elif opt in ('-d', '--do-cld'):
                self.use_cld = True
            elif opt in ('-e', '--enc'):
                self.enc = str(arg)
            elif opt in ('-f', '--filter'):
                if arg == 'all':
                    arg = -1
                self.filter = int(arg)
            elif opt in ('-h', '--help'):
                self.usage()
                sys.exit(0)
            elif opt == '--map-file':
                self.mapfile = str(arg)
            elif opt == '--mcmd':
                self.mcmd = str(arg)
            elif opt in ('-m', '--mode'):
                self.mode = str(arg)
                if self.mode == 'literals':
                    self.mode = SATMinMode.literals
                elif self.mode == 'rules':
                    self.mode = SATMinMode.rules
                elif self.mode == 'blo':
                    self.mode = SATMinMode.blo
                else:
                    self.mode = SATMinMode.multiobj
            elif opt == '--no-ccheck':
                self.noccheck = True
            elif opt == '--opt':
                self.opt = True
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
            elif opt in ('-v', '--verbose'):
                self.verb += 1
            else:
                assert False, 'Unhandled option: {0} {1}'.format(opt, arg)

        self.enc = encmap[self.enc]
        self.files = args

        assert self.approach not in ('mxsat', 'maxsat') or self.mcmd != '', 'No command given to run MaxSAT'

    def usage(self):
        """
            Print usage message.
        """

        print('Usage: ' + os.path.basename(self.command[0]) + ' [options] training-data')
        print('Options:')
        print('        -a, --approach=<string>    Approach to use')
        print('                                   Available values: mxsat, mp92, sat, (default = sat)')
        print('        --approx=<int>             Approximate set cover with at most k attempts')
        print('                                   Available values: [0 .. INT_MAX] (default = 0)')
        print('        --bsymm                    Use symmetry breaking constraints in SAT-based approaches')
        print('        -c, --class=<string>       Class to compute')
        print('                                   Available values: all, best, any-specific-label (default = all)')
        print('                                   Note: if more than one class is chosen and the approach is sat/mp92/minds1,')
        print('                                         the tool pretends that other classes do not exist')
        print('        --cdump                    Dump largest consistent subset of input samples')
        print('        -d, --do-cld               Do D clause calls')
        print('        -e, --enc=<string>         Encoding to use')
        print('                                   Available values: cardn, kmtot, mtot, sortn, tot (default = cardn)')
        print('        -h, --help')
        print('        --map-file=<string>        Path to a file containing a mapping to original feature values. (default: none)')
        print('        --mcmd=<string>            Command to run a MaxSAT solver')
        print('        -m, --mode=<string>        Minimization mode')
        print('                                   Available values: literals, multiobj, rules (default = rules)')
        print('        --no-ccheck                Do not perform consistency check')
        print('        -r, --ranges=<int>         Try to cluster numeric features values into this number of ranges')
        print('                                   Available values: [0 .. INT_MAX] (default = 0)')
        print('        --pdump                    Dump CNF formula to a file')
        print('        --rdump                    Dump resulting CSV table')
        print('        --sep=<string>             Field separator used in input file (default = \',\')')
        print('        -s, --solver=<string>      SAT solver to use')
        print('                                   Available values: g3, lgl, m22, mc, mgh (default = m22)')
        print('        -t, --trim=<int>           Trim unsatisfiable core at most this number of times')
        print('                                   Available values: [0 .. INT_MAX] (default = 0)')
        print('        -v, --verbose              Be more verbose')
