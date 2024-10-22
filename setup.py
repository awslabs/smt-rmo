import os
from setuptools import setup, find_packages

def read(fname):
    return open(os.path.join(os.path.dirname(__file__), fname)).read()

setup(
    name = 'smt_rmo',
    version = '1.0.2',
    description = 'Small utility to reduce the size of and obfuscate an SMTLib input while preserving a solver\'s behavior',
    long_description=read('README.md'),
    author = 'AWS Privacy & Security Automation',
    author_email = 'tlepoint@amazon.com',
    url = 'https://github.com/awslabs/smt-rmo',
    keywords = 'smt-rmo smt',
    license = "Apache",
    entry_points={
        'console_scripts': [
            'smt-rmo = smt_rmo.cli:cli',
        ],
    },
)