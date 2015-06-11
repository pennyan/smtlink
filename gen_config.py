# Copyright (C) 2015, University of British Columbia
# Written (originally) by Yan Peng (13th March, 2014)
#
# License: A 3-clause BSD license.
# See the LICENSE file distributed with this software


# This file generates config.lisp which sets the default
# settings of Smtlink.
#
# Usage:
#   python gen_config.py -i <inputfile>
#                        -o <outputfile>
#                        -p <dir-to-py-exe>
#                        -z <dir-to-py-files>
#                        -e <dir-to-expand-files>
#
# This file can only access default settings for
#
#   1. <dir-to-py-exe> :       The absolute path to where the
#                              Python executable is.
#                              If not set, it gets nil and
#                              Smtlink will report an error.
#
#   2. <dir-to-py-files> :     The path to where the generated
#                              Python files will be stored.
#                              If not set, Python files will be
#                              generated at ~/tmp and gets deleted
#                              every time Smtlink finishes the proof.
#                              If set, generated files won't be
#                              deleted.
#
#   3. <dir-to-expand-files> : The path to where the generated
#                              log files for function expansion
#                              will be stored.
#                              If not set, it gets nil and
#                              no log files will be generated.
#                              This feature is used while debugging
#                              Smtlink. Typical users of Smtlink
#                              won't need to use it.


import io
import sys
import getopt
import re

# (defconst *default-smtlink-config*
#   (make-smtlink-config :dir-interface nil
#                        :dir-files "~/tmp"
#                        :SMT-module "ACL2_to_Z3"
#                        :SMT-class "ACL22SMT"
#                        :smt-cmd nil
#                        :dir-expanded nil))

def is_marker(mk):
    if (mk == ";; Insert-code-for-default-smtlink-config\n"):
        return True
    else:
        return False

def gen_code():
    return "Hello world"

def gen(inf, outf, py_exe, py_file, ex_file):
    wt = open(outf, 'w')
    wline = []

    with open(inf, 'r') as rf:
        rlines = rf.readlines()
    for rline in rlines:
        if (is_marker(rline)):
            wline.append(gen_code(py_exe, py_file, ex_file))
        else:
            wline.append(rline)

    wt.writelines(wlines)
    wt.close()

def main(argv):
    inf = r'config-template.lisp'
    outf = r'config.lisp'
    py_exe = r'python'
    py_file = r'py_files'
    ex_file = r'nil'
    try:
        opts, args = getopt.getopt(argv, "")
    except getopt.GetoptError:
        print "gen_config.py -i <input-file> -o <output-file> -p <python-executable> -z <generated-python-files> -e <generated-expanded-files>"
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-i':
            inf = arg
        elif opt == '-o':
            outf = arg
        elif opt == '-p':
            py_exe = arg
        elif opt == '-z':
            py_file = arg
        elif opt == '-e':
            ex_file = arg
        else:
            print "unrecognizable option: %s" % (opt)
    gen(inf, outf, py_exe, py_file, ex_file)
    print "Finished generating %s file from %s file..." % (outf, inf)


if __name__ == "__main__":
    main(sys.argv[2:])
