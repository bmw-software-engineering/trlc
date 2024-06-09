#!/usr/bin/env python

from trlc.errors import Message_Handler
from trlc.trlc import Source_Manager
import sys

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

# Do something if there are no errors
for obj in symbols.iter_record_objects():
    print(obj.name)
    print(obj.to_python_dict())
