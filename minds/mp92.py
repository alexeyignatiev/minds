#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## mp92.py
##
##  Created on: Dec 20, 2017
##      Author: Filipe Pereira, Alexey Ignatiev
##      E-mail: filipe.pereira.1995@gmail.com, alexey.ignatiev@monash.edu
##

#
#==============================================================================
from minds.rule import Rule
from minds.satr import SATRules
import os
from pysat.card import *
from pysat.examples.lbx import LBX
from pysat.examples.rc2 import RC2
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
import resource
import six
from six.moves import range
import sys

#
#==============================================================================
class MP92Rules(SATRules, object):
    """
        Class implementing the approach from the MP'92 paper.
    """

    def __init__(self, data, options):
        """
            Constructor.
        """

        super(MP92Rules, self).__init__(data, options)

    def encode(self, label, nof_terms):
        """
            Encode the problem of computing a DS of size nof_terms.
        """

        self.nof_terms = nof_terms
        self.nof_samps = len(self.samps)

        enc = CNF()

        # constraint 2
        for j in range(1, self.nof_terms + 1):
            for r in range(1, self.nof_feats + 1):
                enc.append([self.pvar(j, r), self.nvar(j, r)])

        # constraint 3
        if len(self.labels) == 1:  # distinguish one class from all the others
            other_labels = set(self.samps.keys())
        else:  # distinguish the classes under question only
            other_labels = set(self.labels)
        other_labels.remove(label)
        other_labels = sorted(other_labels)
        for j in range(1, self.nof_terms + 1):
            for lb in other_labels:
                for q in self.samps[lb]:
                    cl = []
                    shift = 0
                    for r in range(1, self.nof_feats + 1):
                        if r - 1 in self.data.vmiss[q]:
                            # this feature is missing in q'th sample
                            cl.append(-self.pvar(j, r))
                            cl.append(-self.nvar(j, r))
                            shift += 1
                        else:
                            cl.append(-self.slvar(j, r, q, shift))

                    enc.append(cl)

        # constraint 4
        for j in range(1, self.nof_terms + 1):
            for q in self.samps[label]:
                shift = 0
                for r in range(1, self.nof_feats + 1):
                    if r - 1 in self.data.vmiss[q]:
                        # this feature is missing in q'th sample
                        enc.append([self.pvar(j, r), -self.crvar(j, q + 1)])
                        enc.append([self.nvar(j, r), -self.crvar(j, q + 1)])
                        shift += 1
                    else:
                        enc.append([self.slvar(j, r, q, shift), -self.crvar(j, q + 1)])

        # symmetry breaking constraints
        if self.options.bsymm:
            self.add_bsymm(enc)

        # constraint 5
        if self.options.accuracy == 100.0:
            for q in self.samps[label]:
                enc.append([self.crvar(j, q + 1) for j in range(1, self.nof_terms + 1)])
        else:
            for q in self.samps[label]:
                cv = self.cvvar(q + 1)
                enc.append([-cv] + [self.crvar(j, q + 1) for j in range(1, self.nof_terms + 1)])

                for j in range(1, self.nof_terms + 1):
                    enc.append([-self.crvar(j, q + 1), cv])

            cnum = int(self.options.accuracy * len(self.samps[label]) / 100.0)
            al = CardEnc.atleast([self.cvvar(q + 1) for q in self.samps[label]], bound=cnum, top_id=enc.nv, encoding=self.options.enc)
            if al:
                enc.extend(al.clauses)

        # at most one value can be chosen for a feature
        for feats in six.itervalues(self.ffmap.dir):
            if len(feats) > 2:
                for j in range(1, self.nof_terms + 1):
                    lits = [-self.pvar(j, r + 1) for r in feats]  # atmost1 can be true
                    onev = CardEnc.atmost(lits, top_id=enc.nv, encoding=self.options.enc)
                    enc.extend(onev.clauses)

        # saving comments
        for j in range(1, self.nof_terms + 1):
            for r in range(1, self.nof_feats + 1):
                enc.comments.append('c p({0}, {1}) => v{2}'.format(j, r, self.pvar(j, r)))
                enc.comments.append('c n({0}, {1}) => v{2}'.format(j, r, self.nvar(j, r)))

            for q in range(len(self.data.samps)):
                enc.comments.append('c cr({0}, {1}) => v{2}'.format(j, q + 1, self.crvar(j, q + 1)))

        for n, f in zip(self.data.names[:-1], self.data.feats[:-1]):
            for v in f:
                if self.data.fvmap.dir[(n, v)] > 0:
                    enc.comments.append('c {0} = {1} => positive'.format(n, v))
                else:
                    enc.comments.append('c {0} = {1} => negative'.format(n, v))

        return enc

    def add_bsymm(self, enc):
        """
            Symmetry breaking constraints.
        """

        # Tseitin var for both values missing
        for j in range(1, self.nof_terms + 1):
            for r in range(1, self.nof_feats + 1):
                enc.append([-self.svar(j, r), self.pvar(j, r)])
                enc.append([-self.svar(j, r), self.nvar(j, r)])
                enc.append([self.svar(j, r), -self.pvar(j, r), -self.nvar(j, r)])

        for j in range(2, self.nof_terms + 1):
            enc.append([self.eqvar(j, 0)])
            enc.append([-self.gtvar(j, 0)])
            enc.append([self.gtvar(j, self.nof_feats)])  # enforcing SBPs

            for r in range(1, self.nof_feats + 1):
                # equality constraint
                #
                # left-hand side
                lhs = self.eqvar(j, r)

                # term1
                enc.append([-self.teqvar(j, r, 1), -self.pvar(j, r), self.pvar(j - 1, r)])
                enc.append([-self.teqvar(j, r, 1), self.pvar(j, r), -self.pvar(j - 1, r)])
                enc.append([self.teqvar(j, r, 1), self.pvar(j, r), self.pvar(j - 1, r)])
                enc.append([self.teqvar(j, r, 1), -self.pvar(j, r), -self.pvar(j - 1, r)])

                # term2
                enc.append([-self.teqvar(j, r, 2), -self.nvar(j, r), self.nvar(j - 1, r)])
                enc.append([-self.teqvar(j, r, 2), self.nvar(j, r), -self.nvar(j - 1, r)])
                enc.append([self.teqvar(j, r, 2), self.nvar(j, r), self.nvar(j - 1, r)])
                enc.append([self.teqvar(j, r, 2), -self.nvar(j, r), -self.nvar(j - 1, r)])

                # right-hand side
                cl = [-self.eqvar(j, r - 1),
                        -self.teqvar(j, r, 1),
                        -self.teqvar(j, r, 2)]

                # final clauses
                enc.append([lhs] + cl)
                for l in cl:
                    enc.append([-l, -lhs])

                # 'greater than' constraint
                #
                # left-hand side
                lhs = self.gtvar(j, r)

                # term1
                enc.append([-self.tgtvar(j, r, 1), self.eqvar(j, r - 1)])
                enc.append([-self.tgtvar(j, r, 1), -self.svar(j - 1, r)])
                enc.append([-self.tgtvar(j, r, 1), self.svar(j, r)])
                enc.append([self.tgtvar(j, r, 1), -self.eqvar(j, r - 1), self.svar(j - 1, r), -self.svar(j, r)])

                # term2
                enc.append([-self.tgtvar(j, r, 2), self.eqvar(j, r - 1)])
                enc.append([-self.tgtvar(j, r, 2), -self.nvar(j - 1, r)])
                enc.append([-self.tgtvar(j, r, 2), -self.pvar(j, r)])
                enc.append([self.tgtvar(j, r, 2), -self.eqvar(j, r - 1), self.nvar(j - 1, r), self.pvar(j, r)])

                # right-hand side
                cl = [self.gtvar(j, r - 1),
                        self.tgtvar(j, r, 1),
                        self.tgtvar(j, r, 2)]

                # final clauses
                enc.append([-lhs] + cl)
                for l in cl:
                    enc.append([-l, lhs])

    def pvar(self, j, r):
        """
            True iff literal x_r is not included in rule j.
        """

        return self.idpool.id('p_{0}_{1}'.format(j, r))

    def nvar(self, j, r):
        """
            True iff literal -x_r is not included in rule j.
        """

        return self.idpool.id('n_{0}_{1}'.format(j, r))

    def slvar(self, j, r, q, shift=0):
        """
            True iff literal -x_r is not included in rule j.
        """

        if self.data.samps[q][r - 1 - shift] > 0:
            return self.idpool.id('n_{0}_{1}'.format(j, r))
        else:
            return self.idpool.id('p_{0}_{1}'.format(j, r))

    def svar(self, j, r):
        """
            True iff literal neither value for feature r is included in rule j.
        """

        return self.idpool.id('s_{0}_{1}'.format(j, r))

    def crvar(self, j, q):
        """
            True iff (used) rule j covers sample q.
        """

        return self.idpool.id('cr_{0}_{1}'.format(j, q))

    def eqvar(self, j, r):
        """
            Equality variables for symmetry breaking.
        """

        return self.idpool.id('eq_{0}_{1}'.format(j, r))

    def gtvar(self, j, r):
        """
            'Greater than' variables for symmetry breaking.
        """

        return self.idpool.id('gt_{0}_{1}'.format(j, r))

    def teqvar(self, j, r, i):
        """
            Equality-related Tseitin variables for symmetry breaking.
        """

        return self.idpool.id('te_{0}_{1}_{2}'.format(j, r, i))

    def tgtvar(self, j, r, i):
        """
            'Greater than'-related Tseitin variables for symmetry breaking.
        """

        return self.idpool.id('tg_{0}_{1}_{2}'.format(j, r, i))

    def optimize(self, enc):
        """
            Try to optimize the solution with a MaxSAT solver.
        """

        # a dummy model (everything is deselected)
        model = [v for v in range(enc.nv)]
        all_vars = set()

        # MaxSAT formula to work with
        formula = WCNF()

        # hard clauses
        for cl in enc.clauses:
            formula.append(cl)

        # we have to introduce selector variables (because of hitman)
        top_id = enc.nv

        # soft clauses (unweighted) comprise p and n literals
        for j in range(1, self.nof_terms + 1):
            for r in range(1, self.nof_feats + 1):
                formula.append([self.pvar(j, r)], 1)
                formula.append([self.nvar(j, r)], 1)
                all_vars.add(self.pvar(j, r))
                all_vars.add(self.nvar(j, r))

        if self.options.approx:
            hitman = LBX(formula, use_cld=self.options.use_cld,
                    solver_name=self.options.solver)

            hses = []
            for i, hs in enumerate(hitman.enumerate()):
                hitman.block(hs)
                hses.append(hs)

                if i + 1 == self.options.approx:
                    break

            hs = list(map(lambda v: -formula.soft[v - 1][0], min(hses, key=lambda x: len(x))))
            hitman.delete()
        else:
            hitman = RC2(formula, solver=self.options.solver, adapt=True,
                    exhaust=True, incr=False, minz=False, trim=self.options.trim)

            hs = list(filter(lambda v: v < 0 and -v in all_vars, hitman.compute()))
            hitman.delete()

        # filling the model with the right values
        for e in hs:
            model[-e - 1] = -1

        return model

    def extract_cover(self, label, model):
        """
            Extracts a resulting DS from a model returned by a SAT oracle.
        """

        for j in range(1, self.nof_terms + 1):
            premise = []
            for r in range(1, self.nof_feats + 1):
                if model[self.pvar(j, r) - 1] < 0:
                    id_orig = self.ffmap.opp[r - 1]
                    premise.append(id_orig)
                elif model[self.nvar(j, r) - 1] < 0:
                    id_orig = self.ffmap.opp[r - 1]
                    premise.append(-id_orig)

            # creating the rule
            rule = Rule(fvars=premise, label=label, mapping=self.data.fvmap)

            if self.options.verb:
                print('c1 cover:', str(rule))

            self.covrs[label].append(rule)
            self.cost += len(rule)

        return self.covrs
