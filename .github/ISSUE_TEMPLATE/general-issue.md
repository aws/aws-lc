---
name: AWS-LC General Issue
about: Template
title: ''
labels: ''
assignees: ''

---

### Security issue notifications

If you discover a potential security issue in AWS-LC we ask that you notify AWS Security via our
[vulnerability reporting page](http://aws.amazon.com/security/vulnerability-reporting/). Please do **not** create a
public github issue, if in doubt contact AWS security first.

### Problem:

A short description of what the problem is and why we need to fix it. Add reproduction steps if necessary.

### Solution:

A description of the possible solution in terms of AWS-LC architecture. Highlight and explain any potentially
controversial design decisions taken.

* **Does this change any public APIs?** If yes, explain.
* **Which algorithm(s) will this impact?**

### Requirements / Acceptance Criteria:

What must a solution address in order to solve the problem? How do we know the solution is complete?

* **RFC links:** Links to relevant RFC(s)
* **Related Issues:** Link any relevant issues
* **Will the Usage Guide or other documentation need to be updated?**
* **Testing:** How will this change be tested? Call out new integration tests, functional tests, or particularly
  interesting/important unit tests.
  * **Will this change trigger AWS LibCrypto Formal Verification changes?** Changes to the implementation of verified
    algorithms will require additional changes.
  * **Should this change be fuzz tested?** Will it handle untrusted input? Create a separate issue to track the fuzzing
    work.

### Out of scope:

Is there anything the solution will intentionally NOT address?
