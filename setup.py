import os
from distutils.core import setup

def read(fname):
    return open(os.path.join(os.path.dirname(__file__), fname)).read()

setup(
    name = 'smt_rmo',
    packages = ['smt_rmo'], # this must be the same as the name above
    version = '1.0.1',
    description = 'Small utility to reduce the size of and obfuscate an SMTLib input while preserving a solver\'s behavior',
    long_description=read('README.md'),
    author = 'AWS Privacy & Security Automation',
    author_email = 'tlepoint@amazon.com',
    url = 'https://github.com/awslabs/smt-rmo',
    download_url = 'https://github.com/awslabs/smt-rmo/archive/refs/tags/v1.0.1.tar.gz',
    keywords = 'smt-rmo smt',
    license = "Apache",
    classifiers=[
        "Development Status :: 4 - Beta",
        "Topic :: Utilities",
        "License :: OSI Approved :: Apache License",
    ],
)