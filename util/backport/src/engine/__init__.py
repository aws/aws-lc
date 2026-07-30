"""Part of the backport tool; see ../main.py for the module map.

Present so this is a regular package, not a namespace package. AWS-LC has its
own top-level util/ directory, and without these files Python would merge the
two into one `util` namespace -- which exposes unrelated repo tooling through
this package and lets a same-named module shadow ours depending on sys.path.
"""
