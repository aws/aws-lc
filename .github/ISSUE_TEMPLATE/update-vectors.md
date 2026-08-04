---
name: AWS-LC Update Vectors
about: Template
title: ''
labels: 'vectors'
assignees: 'sgmenda'

---


### Next Steps
- Run `cd third_party/vectors && python3 ./sync.py` locally to update vectors
- Review any new test vectors that are added
- Run `ninja -C build crypto_test` to ensure all tests pass
- Run `python3 util/generate_build_files.py` to update build files
- Verify `cd third_party/vectors && python3 ./sync.py --check` returns success
