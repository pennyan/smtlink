Smtlink
====================

*Smtlink* is a framework for integrating external *SMT* solvers into *ACL2* based on
*clause processors* and *computed hints*.

It supports both ACL2 and *ACL2(r)*. The current default SMT solver integrated is
*Z3*. *SMT-LIB* is expected to be integrated in near future.

### Requirements

* Python 2 is properly installed
* Z3 is properly installed
* ACL2 and its book directory is properly installed
* Smtlink uses Unix commands

### Build Smtlink

* Setup Smtlink configuration in *smtlink-config* in directory $HOME. The
  configuration takes below format
  ```
  interface-dir=...
  smt-module=...
  smt-class=...
  smt-cmd=...
  python-path=...
  ```
  
*  Below table explains what they stands for.
  
  Option        | Explanation                                         | Example
  ------------- | --------------------------------------------------- | -------------
  interface-dir | The directory to SMT solver interface module files  | /Users/.../smtlink/z3_interface
  smt-module    | The module name (i.e. the file name)                | ACL2_to_Z3
  smt-class     | The class name                                      | ACL22SMT
  smt-cmd       | The command for running the SMT solver              | /usr/local/bin/python
  pythonpath    | Set up PAYTHONPATH                                  | /some/path/to/python/libraries
  
* Certify Smtlink to bake setup into certified books

### Load and Setup Smtlink

To use Smtlink, one needs to include book:
```
(include-book "smtlink/top" :dir :sysmtem)
```
Then one needs to enable *tshell* by doing
```
(value-triple (tshell-ensure))
```

### Reference

Yan Peng and Mark R. Greenstreet. [Extending ACL2 with SMT Solvers][publication]
In ACL2 Workshop 2015. October 2015. EPTCS 192. Pages 61-77.

[publication]: https://arxiv.org/abs/1509.06082
