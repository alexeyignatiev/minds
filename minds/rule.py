#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## rule.py
##
##  Created on: Dec 1, 2020
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
class Rule(object):
    """
        Internal representation of a decision set rule.
    """

    def __init__(self, fvars=None, label=None, mapping=None):
        """
            Constructor.
        """

        self.flits = fvars
        self.label = label
        self.fvmap = mapping

    def __str__(self):
        """
            Conversion to human-readable string.
        """

        assert self.label, 'No class assigned'
        assert self.fvmap, 'No mapping from literals to feature-values'

        if self.flits:
            premise = []
            for l in self.flits:
                feat, val = self.fvmap.opp[abs(l)]
                premise.append('{0}\'{1}: {2}\''.format('' if l > 0 else 'not ', feat, val))

            return '{0} => \'{1}: {2}\''.format(', '.join(premise), *self.fvmap.opp[self.label])
        else:
            return 'true => \'{1}: {2}\''.format(*self.fvmap.opp[self.label])

    def __len__(self):
        """
            Return the length of the rule excluding the class label.
        """

        assert self.label, 'No class assigned'
        assert self.fvmap, 'No mapping from literals to feature-values'

        return len(self.flits) if self.flits else 0
