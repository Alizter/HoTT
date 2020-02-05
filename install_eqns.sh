#
#   Script to install Coq-Equations
#

# TODO better specify where to find coq
#arg1=$1

# Find current directroy script lives in
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

# Go to equations directory
cd $DIR/Coq-Equations

# Configure the equations library with the directory
./configure.sh $DIR

# Make the equations plugin
make src/equations_plugin.cmxs

echo Finished compiling, copying and cleaning up

# We copy the compiled plugin to our plugins folder
cp src/equations_plugin.cmxs ../plugins

# Clean object files
make clean

# reset the submodule
git reset --hard
git clean -fx

# Move back to orignal directory
cd $DIR
