#!/usr/bin/env python
#-*- coding:utf-8 -*-
##
## setup.py
##
##  Created on: Jan 22, 2020
##      Author: Alexey Ignatiev
##      E-mail: alexey.ignatiev@monash.edu
##

#
#==============================================================================
try:
    from setuptools import setup, Extension
except ImportError:
    from distutils.core import setup, Extension

from minds import __version__


#
#==============================================================================
LONG_DESCRIPTION = """
*minds* is a Python toolkit, which can be used for computing minimum size
decisions sets, i.e. unordered sets of *if-then* rules. The toolkit represents
a set of pure Python modules, which can be used in a Python script in the
standard way through the provided API. Additionally, it contains an executable
``mds.py``, which can be applied for constructing a smallest size decision set
for a training dataset in CSV.

Details can be found at `https://github.com/alexeyignatiev/minds
<https://github.com/alexeyignatiev/minds>`__.

"""


# finally, calling standard setuptools.setup() (or distutils.core.setup())
#==============================================================================
setup(name='minds-kit',
    packages=['minds'],
    package_dir={},
    version=__version__,
    description='A SAT-based toolkit for learning optimal decision sets',
    long_description=LONG_DESCRIPTION,
    long_description_content_type='text/x-rst; charset=UTF-8',
    license='MIT',
    author='Alexey Ignatiev',
    author_email='alexey.ignatiev@monash.edu',
    url='https://github.com/alexeyignatiev/minds',
    ext_modules=[],
    scripts=['tool/mds.py'],
    cmdclass={},
    install_requires=['pandas', 'python-sat'],
    extras_require = {}
)
