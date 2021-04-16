#!/usr/bin/env python
# -*- coding: utf-8 -*-

from setuptools import setup

def get_README():
    content = ""
    with open("README.md") as f:
        content += f.read()
    return content

setup(
    name="saw",
    python_requires=">=3.7",
    version="0.0.1",
    url="https://github.com/GaloisInc/saw-script",
    project_urls={
        "Source": "https://github.com/GaloisInc/saw/tree/main/saw-remote-api/python",
        "Bug Tracker": "https://github.com/GaloisInc/saw/issues"
    },
    license="BSD",
    description="A scripting library for interacting with the SAW RPC server.",
    long_description=get_README(),
    long_description_content_type="text/markdown",
    author="Galois, Inc.",
    author_email="andrew@galois.com",
    packages=["saw"],
    package_data={"saw": ["py.typed"]},
    zip_safe=False,
    install_requires=[
        "BitVector==3.4.9",
        "mypy==0.812",
        "mypy-extensions==0.4.3",
        "argo-client==0.0.4",
    ],
    classifiers=[
        "Development Status :: 3 - Alpha",
        "License :: OSI Approved :: BSD License",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3.7",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9"
    ],
)
