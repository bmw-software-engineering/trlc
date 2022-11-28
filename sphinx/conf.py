#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# TRLC documentation build configuration file

import os
import sys
sys.path.insert(1, os.path.abspath('..'))

import trlc.version

# -- General configuration ------------------------------------------------

extensions = [
    'sphinx.ext.autodoc',
    'sphinx.ext.autosummary',
    'sphinx.ext.doctest',
    'sphinx.ext.todo',
    'sphinx.ext.coverage',
    'sphinx.ext.mathjax',
    'sphinx.ext.githubpages',
]

templates_path = ['_templates']
source_suffix = '.rst'
master_doc = 'index'

project = 'TRLC'
copyright = '2022, Bayerische Motoren Werke Aktiengesellschaft (BMW AG)'
author = 'Bayerische Motoren Werke Aktiengesellschaft (BMW AG)'

version = trlc.version.TRLC_VERSION
release = trlc.version.TRLC_VERSION

language = None

exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

# If true, the current module name will be prepended to all description
# unit titles (such as .. function::).
#
# add_module_names = True

# The name of the Pygments (syntax highlighting) style to use.
pygments_style = 'sphinx'

# If true, `todo` and `todoList` produce output, else they produce nothing.
todo_include_todos = True


# -- Options for HTML output ----------------------------------------------

html_theme = 'classic'
# html_theme_path = ['../sphinx']
html_theme_options = {
    "stickysidebar": True
}
html_sidebars = {
    "**": ["globaltoc.html", "localtoc.html", "searchbox.html"]
}

html_static_path = ['_static']

autodoc_default_options = {
    "show-inheritance" : True,
    "members" : True,
    "exclude-members": "dump, evaluate",
}
