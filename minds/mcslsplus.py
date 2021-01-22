#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## mcslsplus.py
##
##  Created on: Mar 3, 2020
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
from __future__ import print_function
from math import copysign
from pysat.examples.mcsls import MCSls
from six.moves import range


#
#==============================================================================
class MCSlsPlus(MCSls, object):
    """
        MCSls extended with model computation.
    """

    def __init__(self, formula, use_cld=False, solver_name='m22',
            get_model=False, use_timer=False):
        """
            Constructor.
        """

        super(MCSlsPlus, self).__init__(formula, use_cld, solver_name, use_timer)

        # return a model or not
        self.gmod = get_model

    def compute(self):
        """
            Compute an MCS and the corresponding model.
        """

        self.setd = []
        self.solution = None
        self.bb_assumps = []  # backbone assumptions
        self.ss_assumps = []  # satisfied soft clause assumptions

        if self.oracle.solve():
            # hard part is satisfiable => there is a solution
            self._overapprox()
            self._compute()

            self.solution = [self.smap[-l] for l in self.bb_assumps]

            if self.gmod:
                self.oracle.solve(assumptions=self.ss_assumps)
                self.model = self.oracle.get_model()

        return self.solution

    def get_model(self):
        """
            Get model corresponding to the current MCS.
        """

        if self.gmod:
            self.model = filter(lambda l: abs(l) in self.vmap.i2e, self.model)
            self.model = map(lambda l: int(copysign(self.vmap.i2e[abs(l)], l)), self.model)
            self.model = sorted(self.model, key=lambda l: abs(l))

            return self.model

        return None
