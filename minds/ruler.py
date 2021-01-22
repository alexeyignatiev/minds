#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## ruler.py
##
##  Created on: Dec 4, 2017
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
import collections
import decimal
from minds.lbxplus import LBXPlus
from minds.mcslsplus import MCSlsPlus
from minds.rule import Rule
import os
from pysat.card import *
from pysat.examples.rc2 import RC2, RC2Stratified
from pysat.formula import WCNFPlus
import resource
import socket
import six
from six.moves import range


#
#==============================================================================
class Ruler(object):
    """
        MaxSAT/MCS-based rule enumerator.
    """

    def __init__(self, clusters, target, data, options):
        """
            Constructor.
        """

        self.init_stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime
        self.init_ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime

        # sample clusters for each class
        self.clusters = clusters

        # target class
        self.target = target

        # saving data
        self.data = data

        # saving options
        self.options = options

        # create a MaxSAT formula for rule enumeration
        self.prepare_formula()

        # create and initialize primer
        self.init_solver()

    def prepare_formula(self):
        """
            Prepare a MaxSAT formula for rule enumeration.
        """

        # creating a formula
        self.formula = WCNFPlus()

        # formula's variables
        self.orig_vars = max(self.data.fvmap.opp.keys())
        self.formula.nv = self.orig_vars * 2

        # creating soft clauses and hard p-clauses
        # as well as a mapping between dual-rail variables and input variables
        self.drvmap = {}
        for v in range(1, self.orig_vars + 1):
            if v not in self.data.deleted:
                self.formula.soft.append([-v])
                self.formula.soft.append([-v - self.orig_vars])

                self.formula.hard.append([-v, -v - self.orig_vars])  # p clauses

                self.drvmap[v] = v
                self.drvmap[v + self.orig_vars] = -v

        self.formula.wght = [1 for cl in self.formula.soft]
        self.formula.topw = len(self.formula.soft) + 1

        # hard clauses, discrimination constraints
        self.discrimination()

        # hard clauses, coverage constraints
        self.coverage()

        if self.options.pdump:
            fname = 'rules.{0}@{1}.wcnf'.format(os.getpid(), socket.gethostname())
            self.formula.to_file(fname)

        if self.options.verb:
            print('c1 formula: {0}v, {1}c ({2}h+{3}s)'.format(self.formula.nv,
                len(self.formula.hard) + len(self.formula.soft),
                len(self.formula.hard), len(self.formula.soft)))

    def discrimination(self):
        """
            Add hard clauses enforcing the discrimination constraints,
            each rule discriminates all the instances of wrong classes.
        """

        ncls = len(self.formula.hard)

        for label, instances in self.clusters.items():
            if label != self.target:
                for i in instances:
                    cl = list(map(lambda l: -l if l < 0 else l + self.orig_vars, self.data.samps[i][:-1]))
                    self.formula.hard.append(cl)

        if self.options.verb:
            print('c1 discrimination constraints: {0}h'.format(
                len(self.formula.hard) - ncls))

    def coverage(self):
        """
            Add hard clauses enforcing the coverage constraints such that
            each rule covers at least one instance of the target class.
        """

        topv = self.formula.nv
        ncls = len(self.formula.hard)
        self.tvars = []  # auxiliary variables

        allv = []
        for v in range(1, self.data.fvars + 1):
            allv.append(v)
            allv.append(v + self.orig_vars)
        allv = set(allv)

        # traversing instances of the target class
        for i in self.clusters[self.target]:
            sample = self.data.samps[i]

            # magic to get the set of literals in the sample
            s = set([l if l > 0 else -l + self.orig_vars for l in sample[:-1]])

            # computing the complement of the sample
            compl = allv.difference(s)

            # encoding the complement (as a term) into a set of clauses
            if compl:
                topv += 1
                self.tvars.append(topv)

                compl = sorted(compl)
                for l in compl:
                    self.formula.hard.append([-l, -topv])

                self.formula.hard.append(compl + [topv])

        # add final clause forcing to cover at least one sample
        self.formula.hard.append(self.tvars[:])

        if self.options.plimit:
            self.nof_p = {t: 0 for t in self.tvars}

        if self.options.verb:
            print('c1 coverage constraints: {0}v+{1}h'.format(
                topv - self.formula.nv, len(self.formula.hard) - ncls))

        self.formula.nv = topv

    def init_solver(self):
        """
            Create an initialize a solver for rule enumeration.
        """

        # initializing rule enumerator
        if self.options.primer == 'lbx':
            self.mcsls = LBXPlus(self.formula, use_cld=self.options.use_cld,
                    solver_name=self.options.solver, get_model=True,
                    use_timer=False)
        elif self.options.primer == 'mcsls':
            self.mcsls = MCSlsPlus(self.formula, use_cld=self.options.use_cld,
                    solver_name=self.options.solver, get_model=True,
                    use_timer=False)
        else:  # sorted or maxsat
            MaxSAT = RC2Stratified if self.options.blo else RC2
            self.rc2 = MaxSAT(self.formula, solver=self.options.solver,
                    adapt=self.options.am1, exhaust=self.options.exhaust,
                    trim=self.options.trim, minz=self.options.minz)

            # disabling soft clause hardening
            if type(self.rc2) == RC2Stratified:
                self.rc2.hard = True

    def enumerate(self):
        """
            Enumerate all the rules.
        """

        if self.options.primer in ('lbx', 'mcsls'):
            return self.enumerate_mcsls()
        else:  # sorted or maxsat
            return self.enumerate_sorted()

    def enumerate_mcsls(self):
        """
            MCS-based rule enumeration.
        """

        if self.options.verb:
            print('c1 enumerating rules (mcs-based)')

        self.rules = []

        for mcs in self.mcsls.enumerate():
            mod = self.mcsls.get_model()
            mcs = list(filter(lambda l: l > 0 and abs(l) <= 2 * self.orig_vars, mod))

            rule = self.process_mcs(mcs)

            # recording rule
            self.rules.append(rule)

            # block
            self.mcsls.add_clause([-l for l in mcs])

            if self.options.bsymm:
                # breaking symmetric solutions
                symmpr = sorted(set(self.tvars).difference(set(mod)))
                self.mcsls.add_clause(symmpr)

            # check if there are enough MCSes
            if self.options.plimit:
                model = self.mcsls.get_model()

                i, reduced = 0, False
                while i < len(self.tvars):
                    t = self.tvars[i]
                    if model[t - 1] > 0:
                        self.nof_p[t] += 1

                    if self.nof_p[t] < self.options.plimit:
                        i += 1
                    else:
                        self.tvars[i] = self.tvars[-1]
                        self.tvars.pop()
                        reduced = True

                if reduced:
                    self.mcsls.oracle.add_clause(self.tvars)

                    if not self.tvars:
                        break

        self.mcsls.delete()

        # recording time
        self.stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_stime
        self.ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - self.init_ctime
        self.time = self.stime + self.ctime

        return self.rules

    def enumerate_sorted(self):
        """
            MaxSAT-based rule enumeration.
        """

        if self.options.verb:
            print('c1 enumerating rules (maxsat-based)')

        self.rules = []
        self.mcses = []

        for mod in self.rc2.enumerate():
            mcs = list(filter(lambda l: l > 0 and abs(l) <= 2 * self.orig_vars, mod))

            # blocking the mcs properly
            self.rc2.add_clause([-l for l in mcs])

            # processing it
            rule = self.process_mcs(mcs)

            # recording the mcs for future blocking
            self.mcses.append(mcs)

            # recording rule
            self.rules.append(rule)

            if self.options.bsymm:
                # breaking symmetric solutions
                symmpr = sorted(set(self.tvars).difference(set(mod)))
                self.rc2.add_clause(symmpr)

            # check if there are enough MCSes
            if self.options.plimit:
                model = self.rc2.model

                i, reduced = 0, False
                while i < len(self.tvars):
                    t = self.tvars[i]
                    if model[t - 1] > 0:
                        self.nof_p[t] += 1

                    if self.nof_p[t] < self.options.plimit:
                        i += 1
                    else:
                        self.tvars[i] = self.tvars[-1]
                        self.tvars.pop()
                        reduced = True

                if reduced:
                    self.rc2.add_clause(self.tvars)

                    if not self.tvars:
                        break

        self.rc2.delete()

        # recording time
        self.stime = resource.getrusage(resource.RUSAGE_SELF).ru_utime - self.init_stime
        self.ctime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - self.init_ctime
        self.time = self.stime + self.ctime

        return self.rules

    def process_mcs(self, mcs):
        """
            Extract a rule from MCS.
        """

        # getting the corresponding variables
        rule = Rule(fvars=[self.drvmap[i] for i in mcs], label=self.target,
                mapping=self.data.fvmap)

        # printing rule
        if self.options.verb > 1:
            if self.options.verb > 2:
                print('c1 mcs: {0}'.format(' '.join([str(l) for l in mcs])))

        return rule
