# This file generates config.lisp which sets the default
# settings of Smtlink.
#
# Usage:
#   python gen_config.py -p <dir-to-py-exe>
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


# (defconst *default-smtlink-config*
#   (make-smtlink-config :dir-interface nil
#                        :dir-files "~/tmp"
#                        :SMT-module "ACL2_to_Z3"
#                        :SMT-class "ACL22SMT"
#                        :smt-cmd nil
#                        :dir-expanded nil))


def main (argv):
    return

if __name__ == "__main__":
    main(sys.argv[1:])
