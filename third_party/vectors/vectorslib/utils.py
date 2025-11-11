import sys

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

class Colors:
    RED = "\033[31m" if sys.stdout.isatty() else ""
    GREEN = "\033[32m" if sys.stdout.isatty() else ""
    YELLOW = "\033[33m" if sys.stdout.isatty() else ""
    RESET = "\033[0m" if sys.stdout.isatty() else ""


def info(s: str):
    print(f"{Colors.GREEN}INFO{Colors.RESET}: {s}")


def warning(s: str):
    eprint(f"{Colors.YELLOW}WARNING{Colors.RESET}: {s}")


def error(s: str):
    eprint(f"{Colors.RED}ERROR{Colors.RESET}: {s}")
