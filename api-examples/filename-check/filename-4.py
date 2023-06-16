#!/usr/bin/env python

from trlc.errors import Message_Handler
from trlc.trlc import Source_Manager
from trlc import ast
import sys
import os

# Create Source_Manager
mh = Message_Handler()
sm = Source_Manager(mh)

# Read all .rsl, .check, and .trlc files
# in the given directory
sm.register_directory(".")

# Parse and stop if there are errors
symbols = sm.process()
if symbols is None:
    sys.exit(1)

# Do something if there are no errors
pkg_example   = symbols.lookup_assuming(
    mh                = mh,
    name              = "Example",
    required_subclass = ast.Package)
req_base_type = pkg_example.symbols.lookup_assuming(
    mh                = mh,
    name              = "Requirement",
    required_subclass = ast.Record_Type)

for obj in symbols.iter_record_objects():
    values = obj.to_python_dict()

    if not obj.n_typ.is_subclass_of(req_base_type):
        continue

    if values["illustration"] is not None and \
       not os.path.isfile(values["illustration"]):

        mh.error(location = obj.field["illustration"].location,
                 message  = "is not a file",
                 fatal    = False,
                 user     = True)
