import setuptools


with open("README.md") as fp:
    long_description = fp.read()


setuptools.setup(
    name="AWS-LC CI",
    version="0.0.1",

    description="AWS-LC CI python environment.",
    long_description=long_description,
    long_description_content_type="text/markdown",

    author="AWS-LC",

    package_dir={"": "cdk"},
    packages=setuptools.find_namespace_packages(where="cdk"),

    install_requires=[
        # CDK dependencies.
        "aws-cdk-lib==2.177.0",
        "constructs==10.4.2",
        # PyYAML is a YAML parser and emitter for Python. Used to read build_spec.yaml.
        "pyyaml==6.0.2",
        # A formatter for Python code.
        "yapf==0.43.0",
        # Introduced by benchmark framework.
        "boto3==1.36.12",
        # Introduced by Android Device Farm CI.
        "requests",
        "arnparse==0.0.2",
        "urllib3==2.2.3"
    ],

    python_requires=">=3.6",

    classifiers=[
        "Development Status :: 4 - Beta",

        "Intended Audience :: Developers",

        "License :: OSI Approved :: Apache Software License",

        "Programming Language :: JavaScript",
        "Programming Language :: Python :: 3 :: Only",
        "Programming Language :: Python :: 3.6",
        "Programming Language :: Python :: 3.7",
        "Programming Language :: Python :: 3.8",

        "Topic :: Software Development :: Code Generators",
        "Topic :: Utilities",

        "Typing :: Typed",
    ],
)
