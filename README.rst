minds: a SAT-based toolkit for learning optimal decision sets
=============================================================

*minds* is a Python toolkit, which can be used for computing minimum size
decisions sets, i.e. unordered sets of *if-then* rules [1]_. The toolkit
represents a set of pure Python modules, which can be used in a Python script
in the standard way through the provided API. Additionally, it contains an
executable ``mds.py``, which can be applied for constructing a smallest size
decision set for a training dataset in `CSV
<https://en.wikipedia.org/wiki/Comma-separated_values>`__.

.. [1] Here the size can be defined as the number of rules of the decision
   set, or the total number of literals used.

Getting started
---------------

Before using *minds*, make sure you have the following Python packages
installed:

-  `pandas <https://pandas.pydata.org/>`__
-  `PySAT <https://github.com/pysathq/pysat>`__


Please, follow the installation instructions on these projects' websites to
install them properly. (If you spot any other package dependency not listed
here, please, let us know.)

Also, running some of the algorithms require `CPLEX
<https://www.ibm.com/analytics/cplex-optimizer>`__ and/or `Gurobi
<https://www.gurobi.com/>`__ as well as their Python bindings to be installed.

Finally, to install *minds*, it should suffice to do (alternatively, set it up
from this GitHub repository):

::

   $ pip install minds-kit

Usage
-----

The ``mds.py`` executable provided by the toolkit serves as a simple example
of how the toolkit can be used. It has a number of command-line options and
their list can be seen by running:

::

   $ mds.py -h

Minimizing the number of rules
------------------------------

In order to minimize the number of rules used in the target decision set, a
user can apply the approaches proposed in the `IJCAR'18 paper
<https://alexeyignatiev.github.io/assets/pdf/ipnms-ijcar18-preprint.pdf>`__.
For instance, the following command can be used to apply the SAT-based
formulation of *MinDS2* and exploit the Glucose3 SAT solver (note that any
other SAT solver available in PySAT can be used):

::

   $ mds.py -a satr -s glucose3 -v <dataset.csv>

To apply the *MP92* model, run:

::

   $ mds.py -a mp92 -s glucose3 -v <dataset.csv>

To apply the *MinDS1* model, run:

::

   $ mds.py -a minds1 -s glucose3 -v <dataset.py>

Any of these approaches can be augmenter with the option ``--opt``, which
enables MaxSAT-based minimization of the number of literals used once the
optimal number of rules is obtained and *fixed*, e.g.:

::

   $ mds.py -a satr --opt -s glucose3 -v <dataset.csv>

If option ``'--approx <int>'`` is given, the MaxSAT call will be replaced with
a series of ``<int>`` MCSes enumerated to approximate the exact MaxSAT
solution.

Minimizing the total number of literals
---------------------------------------

Our `recent CP'20 paper
<https://alexeyignatiev.github.io/assets/pdf/yisb-cp20-preprint.pdf>`__
proposed a novel SAT- and MaxSAT-based approach to minimizing the total number
of literals used in the target decision set. An example of how this can be
done using the ``mds.py`` script follows:

::

   $ mds.py -a satl -s glucose3 -v <dataset.csv>

Here, one can replace the argument value ``'satl'`` with values ``satls`` to
split the computation process by classes, or with values ``mxsatl`` and
``mxsatls`` to achieve the result by exploiting MaxSAT solvers (instead of
iterative SAT solving).

Sparse decision sets can be constructed by running:

::

   $ mds.py -a sparse --lambda <float> -s glucose3 -v <dataset.csv>

Here, the value of ``'--lambda'`` is the regularization cost parameter, which
equals 0.005 *by default*. It indicates how much adding a literal/rule to the
decision set costs with respect to the overall accuracy increase (see `the
paper
<https://alexeyignatiev.github.io/assets/pdf/yisb-cp20-preprint.pdf>`__
for details).

Two-stage approach
------------------

Our `recent paper at AAAI'21
<https://alexeyignatiev.github.io/assets/pdf/ilsms-aaai21-preprint.pdf>`__
proposed an efficient two-stage approach to computing smallest size decision
sets, the first stage of which consists in enumerating all possible rules for
given training data while the second stage consists of solving the set cover
problem for selecting an optimal set of rules for each class. This approach
can be used to compute a decision set with either a smallest number of rules
or a smallest number of literals. The approach can be invoked by running:

::

   $ mds.py -a 2stage -B -C gurobi --s glucose3 -v <dataset.csv>

Here, option ``'-B'`` enables breaking symmetric rules to enumerate at stage
1; options ``'-C gurobi'`` forces the tool to use Gurobi for solving the set
cover problem of stage 2 (note that one can instead opt to use ``'rc2'`` or
``'cplex'``).

Tweaking the MaxSAT solver
--------------------------

As some of the developed algorithms apply MaxSAT solving, it is sometimes
important to get the best performance of the underlying MaxSAT solver. The
``mds.py`` tool provides a number of command-line options to tweak the
internal heuristics of the award-winning MaxSAT solver RC2 used in *minds*:

-  ``-1`` - to detect AtMost1 constraints
-  ``-b`` - to apply Boolean lexicographic optimization (BLO)
-  ``-m`` - to apply heuristic minimization of unsatisfiable cores
-  ``-t`` - to *trim* unsatisfiable cores (at most) a given number of times
-  ``-x`` - to *exhaust* unsatisfiable cores

You may want to use any combination of these. Also, note that *none of them*
are enabled by default. The techniques enabled by these command-line
parameters are detailed in `the paper describing RC2
<https://alexeyignatiev.github.io/assets/pdf/imms-jsat19-preprint.pdf>`__.
Read it if you are interested.

Using the API
-------------

As mentioned above, the toolkit's functionality can be accessed through the
Python API. At this point, *minds* does not offer an easy-to-use API *à la*
`scikit <https://scikit-learn.org/>`__ although this should hopefully be fixed
in the future. The ``mds.py`` tool provided with the toolkit can serve as an
example of how the functionality can be used. Some of the major points are
also outlined below:

.. code:: python

   from minds.data import Data
   from minds.check import ConsistencyChecker
   from minds.options import Options
   from minds.twostage import TwoStageApproach

   # setting the necessary parameters
   options = Options()
   options.approach = '2stage'
   options.solver = 'glucose3'
   options.cover = 'gurobi'
   options.bsymm = True  # applying symmetry breaking
   options.verb = 0  # verbosity level

   # reading data from a CSV file
   data = Data(filename='some-dataset.csv', separator=',')

   # data may be inconsistent/contradictory
   checker = ConsistencyChecker(data, options)
   if checker.status and checker.do() == False:
       # if we do not remove inconsistency, our approach will fail
       checker.remove_inconsistent()

   # creating and calling the solver
   ruler = TwoStageApproach(data, options)
   covers = ruler.compute()

   # printing the result rules for every label/class to stdout
   for label in covers:
       for rule in covers[label]:
           print('rule:', rule)

Note that all the algorithms make use of the ``Data`` class for representing
the data internally. An object of class dat can be created for a given CSV
file, or alternatively for a *pandas'* DataFrame object:

.. code:: python

   import pandas
   dframe = pandas.read_csv('some-dataset.csv')
   data = Data(dataframe=dframe)

It is also crucial that the data to be given to *any of the algorithms* must
be consistent, i.e. there must not be two data instances mapping the same
feature values to different classes. This can be checked by the use of
``ConsistencyChecker``, which determines the *largest portion* of the dataset
that is consistent. See the code above for how it can be used.

Alternatively, especially if you work with a pandas ``DataFrame``, it may be
easier and/or more convenient for you to get rid of inconsistency directly on
your own by traversing and "fixing" the ``DataFrame``.

Citation
--------

If any of the decision set learning algorithms of *minds* has been significant
to a project that leads to an academic publication, please, acknowledge that
fact by citing the corresponding paper where it was proposed:

::

    @inproceedings{ipnms-ijcar18,
      author    = {Alexey Ignatiev and
                   Filipe Pereira and
                   Nina Narodytska and
                   Joao Marques{-}Silva},
      title     = {A SAT-Based Approach to Learn Explainable Decision Sets},
      booktitle = {{IJCAR}},
      pages     = {627--645},
      year      = {2018},
      url       = {https://doi.org/10.1007/978-3-319-94205-6\_41},
      doi       = {10.1007/978-3-319-94205-6\_41}
    }

    @inproceedings{yilbs-cp20,
      author    = {Jinqiang Yu and
                   Alexey Ignatiev and
                   Peter J. Stuckey and
                   Pierre {Le Bodic}},
      title     = {Computing Optimal Decision Sets with {SAT}},
      booktitle = {{CP}},
      pages     = {952--970},
      year      = {2020},
      url       = {https://doi.org/10.1007/978-3-030-58475-7\_55},
      doi       = {10.1007/978-3-030-58475-7\_55}
    }

    @inproceedings{ilsms-aaai21,
      author    = {Alexey Ignatiev and
                   Edward Lam and
                   Peter J. Stuckey and
                   Joao Marques{-}Silva},
      title     = {A Scalable Two Stage Approach to Computing Optimal Decision Sets},
      booktitle = {AAAI},
      year      = {2021}
    }

License
-------

minds is licensed under `MIT <LICENSE.txt>`__.
