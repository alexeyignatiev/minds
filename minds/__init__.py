#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## __init__.py
##
##  Created on: Jan 19, 2021
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

# current version
#==============================================================================
VERSION = (0, 0, 1, "dev", 2)


# PEP440 Format
#==============================================================================
__version__ = "%d.%d.%d.%s%d" % VERSION if len(VERSION) == 5 else \
              "%d.%d.%d" % VERSION


# all submodules
#==============================================================================
__all__ = ['check', 'cover', 'data', 'dscheck', 'lbxplus', 'mcslsplus',
        'minds1', 'mp92', 'mxsatl', 'mxsatls', 'mxsatsp', 'options',
        'public_interface', 'rule', 'ruler', 'satl', 'satls', 'satr',
        'twostage']

