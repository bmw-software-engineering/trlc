# TRLC Tutorial (Basic Concepts)

This is part of the [TRLC Tutorial](TUTORIAL.md).

## Motivation

The TRLC check language allows you to enforce internal consistency for
requirements, but there are limitations to its scope. For example
consider this requirement type:

```
package Example

type Requirement {
   description           String
   illustration optional String
}
```

The `illustration` field is supposed to allow us to specify a filename
for a picture that relates to the requirement, for example a UI
mockup. But we cannot check that the file exists in the check language.

However we can create a custom tool that checks this using the [TRLC
Python API](https://bmw-software-engineering.github.io/trlc/).

We also need a few requirements to test our tool:

```
package Example

Requirement good_1 {
  description = "this is a good example"
}

Requirement good_2 {
  description  = "this is another good example"
  illustration = "example.png"
}

Requirement bad_1 {
  description  = "this is a bad example"
  illustration = "bad.png"
}
```

## Getting the API set up

Lets go over the absolute minimal example to set up the API.  First we
need to import a few things: the
[Message_Handler](https://bmw-software-engineering.github.io/trlc/manual/errors.html#trlc.errors.Message_Handler)
is the mechanism for issuing messages, and the
[Source_Handler](https://bmw-software-engineering.github.io/trlc/manual/infrastructure.html#trlc.trlc.Source_Manager)
is the main driver for the TRLC parser. There are other useful things
we can import but for now this is sufficient.

```
#!/usr/bin/env python

from trlc.errors import Message_Handler
from trlc.trlc import Source_Manager
import sys
```

Next we need create an instance of the source manager:

```
mh = Message_Handler()
sm = Source_Manager(mh)
```

Then we need to tell the source manager where it can find the
files. For this example we'll just use the current directory. Note
that the
[register_directory](https://bmw-software-engineering.github.io/trlc/manual/infrastructure.html#trlc.trlc.Source_Manager.register_directory)
method also looks into the sub-directories of the given directory. You
can also provide individual files to the tool using
[register_file](https://bmw-software-engineering.github.io/trlc/manual/infrastructure.html#trlc.trlc.Source_Manager.register_file),
but often register_directory is a much easier way to set up the tools.

```
sm.register_directory(".")
```

After all files or directories have been registered we need to parse
them. The
[process](https://bmw-software-engineering.github.io/trlc/manual/infrastructure.html#trlc.trlc.Source_Manager.process)
method parses all files, and on success returns a
[Symbol_Table](https://bmw-software-engineering.github.io/trlc/manual/ast.html#trlc.ast.Symbol_Table)
containing everything (types, checks, requirements, etc.). If there is
an error (used defined check or syntax error) then nothing is
returned. I.e. once the API lets you have the symbol table you know
that everything is well formed and validated.


```
symbols = sm.process()
if symbols is None:
    sys.exit(1)
```

Finally, lets do something simple to see what happens. Here we just
iterate overt all the objects and print them.

```
for obj in symbols.iter_record_objects():
    print(obj.name)
    print(obj.to_python_dict())
```

When running this script, we can see output like this:

```
$ ./filename-1.py
good_1
{'illustration': None, 'description': 'this is a good example'}
good_2
{'illustration': 'example.png', 'description': 'this is another good example'}
bad_1
{'illustration': 'bad.png', 'description': 'this is a bad example'}
```

## First attempt

Now that we can see that the API works, we can implement our check in
a very basic way.

```
for obj in symbols.iter_record_objects():
    values = obj.to_python_dict()

    if values["illustration"] is not None and \
       not os.path.isfile(values["illustration"]):
        print("error: %s for requirement %s is not a file" %
              (values["illustration"],
               obj.name))
```

When running the script, we actually get what we want:

```
$ ./filename-2.py
error: bad.png for requirement bad_1 is not a file
```

While this is useful, there are a lot of issues here:

* We use print. This works, but the TRLC Message_Handler is designed
  to write error messages in a much nicer way.
* If we have another requirement type, then this check will just crash
  as "illustration" will not be in the dictionary
* If we have another requirement type, where "illustration" exists but
  means something very different (it might be a Boolean) we might
  perform this check in error

## Second attempt: better messages

Let's get better error messages first. We can use the Message_Handler
instead.

This is what we do:

```
for obj in symbols.iter_record_objects():
    values = obj.to_python_dict()

    if values["illustration"] is not None and \
       not os.path.isfile(values["illustration"]):

        mh.error(location = obj.field["illustration"].location,
                 message  = "is not a file",
                 fatal    = False,
                 user     = True)
```

This is quite different. The message is much shorter, and the location
is the place where the message should be anchored. When running this
check we can now see this:

```
$ ./filename-3.py
  illustration = "bad.png"
                 ^^^^^^^^^ example.trlc:14: check error: is not a file
```

This is way more helpful than the original print statement: you get to
see what is wrong, and where.

In the first version of our check we just convert the entire object to
a Python dictionary using
[to_python_dict](https://bmw-software-engineering.github.io/trlc/manual/ast.html#trlc.ast.Record_Object.to_python_dict). This
is a helpful method designed to allow you to write quick and dirty
tools; but there is a lot if information missing. For example you can
see what values a requirement has, but you have no idea what it
actually is or where it came from. However the API exposes this
information as it allows access to the internal AST (abstract syntax
tree).

The
[error](https://bmw-software-engineering.github.io/trlc/manual/errors.html#trlc.errors.Message_Handler.error)
method allows you to create messages, but you need to provide at least
two things: where the error is (via a
[Location](https://bmw-software-engineering.github.io/trlc/manual/errors.html#trlc.errors.Location))
and a message.

Everything in TRLC has a location attribute, and in this example we
use the location of the actual record field of the
[Record_Object](https://bmw-software-engineering.github.io/trlc/manual/ast.html#trlc.ast.Record_Object)
to anchor the message.

## Final solution: type checking

The final issue we should fix is making sure the object we look at is
a Requirement type.

This is a bit more complex, as testing the name of the type
(e.g. `obj.e_typ.name == "Requirement"` is not enough: if we extend
the Requirement type then we also want this check to apply.

So first we need to find the actual
[Record_Type](https://bmw-software-engineering.github.io/trlc/manual/ast.html#trlc.ast.Record_Type)
that we've defined: first by finding the Example package, and then by
searching its symbol table for the type.

Then we can use the is_subclass_of test for the type of the object to
determine if it is a Requirement or inherits from Requirement. If not,
we move on to the next object.

```
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

    if not obj.e_typ.is_subclass_of(req_base_type):
        continue

    if values["illustration"] is not None and \
       not os.path.isfile(values["illustration"]):

        mh.error(location = obj.field["illustration"].location,
                 message  = "is not a file",
                 fatal    = False,
                 user     = True)
```

That's it, we're done! We now have a pretty robust check that makes
sure all `illustration` fields in `Requirement` types actually exist.

You can find the final script and example files in
[api-examples/filename-check](https://github.com/bmw-software-engineering/trlc/tree/main/api-examples/filename-check). The
final script is `filename-4.py`.
