#!/usr/bin/bash

git archive HEAD --prefix=logrel-coq/ --format=zip -o logrel-coq.zip
git submodule --quiet foreach 'cd $toplevel; cd ..; zip -ru logrel-coq/logrel-coq.zip logrel-coq/$sm_path'
