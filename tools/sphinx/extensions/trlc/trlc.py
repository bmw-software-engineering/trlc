from collections import defaultdict
from pathlib import PurePosixPath

from sphinx import addnodes
from sphinx.application import Sphinx
from sphinx.directives import ObjectDescription
from sphinx.domains import Domain, Index
from sphinx.roles import XRefRole
from sphinx.util import logging
from sphinx.util.nodes import make_refnode

logger = logging.getLogger(__name__)


def _pretty_location(docname: str, line: int | None = None) -> str:
    """Return a short, human-readable source location.

    Bazel sandboxes produce very long absolute paths that are not clickable in
    VS Code terminals.  This helper strips all leading path components up to
    (and including) ``_sources/`` so that only the workspace-relative document
    path remains.  A line number is appended when available.
    """
    path = docname
    marker = "_sources/"
    idx = path.find(marker)
    if idx != -1:
        path = path[idx + len(marker) :]
    # Ensure .rst suffix for clickability
    if not path.endswith(".rst"):
        path += ".rst"
    if line is not None:
        return f"{path}:{line}"
    return path


class RequirementsDirective(ObjectDescription):
    has_content = True
    required_arguments = 1
    option_spec = {}

    def handle_signature(self, sig, signode):
        signode += addnodes.desc_name(text=sig)
        return sig

    def add_target_and_index(self, name, sig, signode):
        signode["ids"].append("requirement" + "-" + sig)
        requirements = self.env.get_domain("requirement")
        requirements.add_requirement(sig)


class RequirementsIndex(Index):
    name = "requirement"
    localname = "Requirement Index"
    shortname = "Requirement"

    def generate(self, docnames=None):
        content = defaultdict(list)

        # sort the list of requirements in alphabetical order
        requirements = self.domain.get_objects()
        requirements = sorted(requirements, key=lambda requirement: requirement[0])

        # group by first letter for name
        for _name, dispname, typ, docname, anchor, _priority in requirements:
            safe_char = dispname[0] if dispname and dispname[0].isalpha() else "?"
            heading = safe_char.upper()
            content[heading].append(
                (
                    dispname,
                    0,
                    docname,
                    anchor,
                    docname,
                    "",
                    typ,
                )
            )

        content = sorted(content.items(), key=lambda t: t[0].lower())

        return content, True


class RequirementsDomain(Domain):
    name = "requirement"
    roles = {
        "upstream-ref": XRefRole(),
        "downstream-ref": XRefRole(),
    }
    directives = {
        "definition": RequirementsDirective,
    }
    indices = (RequirementsIndex,)
    initial_data = {
        "requirements": [],
    }

    def get_full_qualified_name(self, node):
        return f"requirement.{node.arguments[0]}"

    def get_objects(self):
        yield from self.data["requirements"]

    def resolve_xref(self, env, fromdocname, builder, typ, target, node, contnode):
        match = [
            (docname, anchor)
            for name, sig, typ, docname, anchor, prio in self.get_objects()
            if sig == target
        ]
        if len(match) == 1:
            todocname, targ = match[0]
            return make_refnode(builder, fromdocname, todocname, targ, contnode, targ)
        elif len(match) > 1:
            loc = _pretty_location(fromdocname, node.line if node else None)
            logger.warning(
                "(%s):  '%s' is ambiguous (%d targets found)",
                loc,
                target,
                len(match),
            )
        else:
            loc = _pretty_location(fromdocname, node.line if node else None)
            logger.warning(
                "(%s):  '%s' not found",
                loc,
                target,
            )
        return None

    def add_requirement(self, signature):
        name = f"requirement.{signature}"
        anchor = f"requirement-{signature}"

        self.data["requirements"].append(
            (name, signature, "Requirement", self.env.docname, anchor, 0)
        )

    def merge_domaindata(self, docnames, otherdata):
        self.data["requirements"].extend(otherdata["requirements"])


def setup(app: Sphinx):
    app.add_domain(RequirementsDomain)

    return {
        "version": "0.1",
        "parallel_read_safe": True,
        "parallel_write_safe": True,
    }
