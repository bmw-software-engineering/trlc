TRLC Python API
===============

This is description for the end-user facing TRLC API.

First you need to create a source manager and feed it files::

  from trlc.errors import Message_Handler
  from trlc.trlc import Source_Manager

  # Create Source_Manager
  mh = Message_Handler()
  sm = Source_Manager(mh)

  # Read all .rsl and .trlc files
  # in the given directory
  sm.register_directory("path/to/trlc_files")

Once all files are registered, you call the process function to parse
and validate the input (both language defined validation and
user-supplied checks)::

  # Parse and stop if there are errors
  symbols = sm.process()
  if symbols is None:
      sys.exit(1)

This operation returns a :class:`~trlc.ast.Symbol_Table` if there are
no errors. The most likely thing you will want to do is to iterate
over all requirements (i.e. :class:`~trlc.ast.Record_Object`) that
have been declared::

  # Do something if there are no errors
  for obj in symbols.iter_record_objects():
      print(obj.name)
      print(obj.to_python_dict())

Most likely that is enough, but you can access the entire parse tree
from this API.

.. toctree::
   :maxdepth: 2
   :caption: TRLC API Docs

   manual/infrastructure
   manual/errors
   manual/ast

.. toctree::
  :caption: Iteration API by Section

  section_api
