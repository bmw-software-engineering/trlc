#!/usr/bin/env python

from trlc.errors import Message_Handler
from trlc.trlc import Source_Manager
import sys
import os

# Create Source_Manager
mh = Message_Handler()
sm = Source_Manager(mh)

# Read all .rsl and .trlc files
# in the given directory
sm.register_directory(".")

# Parse and stop if there are errors
symbols = sm.process()
if symbols is None:
    sys.exit(1)

failed = False

# Do something if there are no errors
for obj in symbols.iter_record_objects():
    values = obj.to_python_dict()

    if values["illustration"] is not None and \
       not os.path.isfile(values["illustration"]):

        mh.error(location = obj.field["illustration"].location,
                 message  = "is not a file",
                 fatal    = False,
                 user     = True)

        failed = True

if failed is True:
    sys.exit(1)
