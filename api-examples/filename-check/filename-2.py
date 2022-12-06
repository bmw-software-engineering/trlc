#!/usr/bin/env python

from trlc.errors import Message_Handler
from trlc.trlc import Source_Manager
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
for obj in symbols.iter_record_objects():
    values = obj.to_python_dict()
    if values["illustration"] is not None and \
       not os.path.isfile(values["illustration"]):
        print("error: %s for requirement %s is not a file" %
              (values["illustration"],
               obj.name))
