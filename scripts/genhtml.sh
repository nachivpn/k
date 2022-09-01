#!/bin/sh

set -e -u

REPO=nachivpn/k
AGDA_FILE=src/Everything.agda

GH_PAGES_BRANCH=gh-pages
GH_PAGES_HTML_DIR=html

REPO_PULL_URL=https://github.com/$REPO.git
REPO_PUSH_URL=git@github.com:$REPO.git
TREE_BASE_URL=https://github.com/$REPO/tree

usage () {
	cat <<EOF
Usage: $_SCRIPTNAME BRANCH
EOF
}

usage_and_exit_zero () {
	usage
	exit 0
}

usage_and_exit_nonzero () {
	usage
	exit 2
}

clean_and_exit () {
  [ -z "${HTML_BUILD_DIR:+x}"     ] || [ ! -d "$HTML_BUILD_DIR"     ] || rm -r -f $HTML_BUILD_DIR
  [ -z "${REPO_CLONE_DIR:+x}"     ] || [ ! -d "$REPO_CLONE_DIR"     ] || rm -r -f $REPO_CLONE_DIR
  [ -z "${GH_PAGES_CLONE_DIR:+x}" ] || [ ! -d "$GH_PAGES_CLONE_DIR" ] || rm -r -f $GH_PAGES_CLONE_DIR
	exit $_EXITCODE
}

file_extension () {
  [ -n "$1" ] || { echo 'file_extension: missing operand'; return 1; }
  echo $1 | awk -F . '{ if (NF > 1) print $NF }'
}

_SCRIPTNAME=$(basename $0)

[ $# -ne 1 ] && usage_and_exit_nonzero

BRANCH=$1

trap '_EXITCODE=$?; trap - INT QUIT TERM EXIT; clean_and_exit' INT QUIT TERM EXIT

echo -n "Cloning $BRANCH..."
REPO_CLONE_DIR=$(mktemp -d --tmpdir ${_SCRIPTNAME}_repo.XXXXXXX)
git clone -q --single-branch --no-tags -b $BRANCH $REPO_PULL_URL $REPO_CLONE_DIR
echo ' Done.'
HTML_BUILD_DIR=$(mktemp -d --tmpdir ${_SCRIPTNAME}_html.XXXXXXX)
if [ -d _build ] && [ ! -e $REPO_CLONE_DIR/_build ]
then
  echo -n 'Copying _build directory...'
  cp -r _build $REPO_CLONE_DIR/
  echo ' Done.'
fi
echo -n "Type checking $AGDA_FILE..."
(
  cd $REPO_CLONE_DIR/$(dirname $AGDA_FILE)
  agda -v 0 $(basename $AGDA_FILE)
)
echo ' Done.'
echo -n "Generating html for $AGDA_FILE..."
(
  cd $REPO_CLONE_DIR/$(dirname $AGDA_FILE)
  agda -v 0 --html --html-dir=$HTML_BUILD_DIR $(basename $AGDA_FILE)
  COMMIT_HASH=$(git show -s --format=%H HEAD)
  TREE_URL=$TREE_BASE_URL/$COMMIT_HASH
  #AGDA_FILE_EXT=.$(file_extension $AGDA_FILE)
  #HTML_FILE=$HTML_BUILD_DIR/$(basename $AGDA_FILE $AGDA_FILE_EXT).html
  find $HTML_BUILD_DIR -name \*.html -exec sed -i -e "s|</body>|<hr><p style=\"font-family: monospace\">Generated from commit <a href=\"$TREE_URL\">$COMMIT_HASH</a>.</p>&|" {} \;
)
echo ' Done.'

echo -n "Updating $GH_PAGES_BRANCH..."
GH_PAGES_CLONE_DIR=$(mktemp -d --tmpdir ${_SCRIPTNAME}_gh-pages.XXXXXXX)
git clone -q --single-branch --no-tags -b $GH_PAGES_BRANCH $REPO_PULL_URL $GH_PAGES_CLONE_DIR
git -C $GH_PAGES_CLONE_DIR rm -q -r $GH_PAGES_HTML_DIR
cp -r $HTML_BUILD_DIR $GH_PAGES_CLONE_DIR/$GH_PAGES_HTML_DIR
git -C $GH_PAGES_CLONE_DIR add $GH_PAGES_HTML_DIR
if ! git -C $GH_PAGES_CLONE_DIR diff-index --quiet --cached HEAD
then
  echo
  git -C $GH_PAGES_CLONE_DIR commit -q -m "Update html folder"
  DIFF=x
  while [ "$DIFF" != n ] && [ "$DIFF" != y ]
  do
    echo -n "Preview changes to $GH_PAGES_BRANCH? [y/N] "
    read DIFF
    [ -n "$DIFF" ] || DIFF=n
  done
  if [ "$DIFF" = y ]
  then
    git -C $GH_PAGES_CLONE_DIR log --format=fuller -p @{u}..
  else
    git -C $GH_PAGES_CLONE_DIR --no-pager log --format=fuller @{u}..
  fi
  PUSH=x
  while [ "$PUSH" != n ] && [ "$PUSH" != y ]
  do
    echo -n "Push changes to $GH_PAGES_BRANCH? [y/N] "
    read PUSH
    [ -n "$PUSH" ] || PUSH=n
  done
  if [ "$PUSH" = y ]
  then
    git -C $GH_PAGES_CLONE_DIR push $REPO_PUSH_URL -q
    echo 'Done.'
  else
    echo 'Aborted.'
  fi
else
  echo ' Done. (was already up to date)'
fi
