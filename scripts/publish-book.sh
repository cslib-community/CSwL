#!/usr/bin/env bash
# Publishes the `student` build to the `book` repo:
#
#   _out/student/lean/  -> book@main      (Lake project — GitHub Classroom
#                                           assignment / student template)
#   _out/student/html/  -> book@gh-pages  (published site, GitHub Pages)
#
# `book`'s two branches are unrelated histories: `main` is a Lake project,
# `gh-pages` is a static site. Each branch's tree is replaced wholesale by
# the corresponding `_out/student/` output and committed if it changed.
#
# Usage: scripts/publish-book.sh [book-dir]
# book-dir defaults to ../book (sibling of this CSwL checkout).

set -euo pipefail

CSWL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BOOK_DIR="$(cd "${1:-"$CSWL_DIR/../book"}" && pwd)"

LEAN_SRC="$CSWL_DIR/_out/student/lean"
HTML_SRC="$CSWL_DIR/_out/student/html"

for d in "$LEAN_SRC" "$HTML_SRC"; do
  [ -d "$d" ] || { echo "error: $d não existe — rode 'make student' primeiro" >&2; exit 1; }
done

[ -d "$BOOK_DIR/.git" ] || { echo "error: $BOOK_DIR não é um repositório git" >&2; exit 1; }

CSWL_SHA="$(git -C "$CSWL_DIR" rev-parse --short HEAD)"
ORIG_BRANCH="$(git -C "$BOOK_DIR" branch --show-current)"

cleanup() {
  git -C "$BOOK_DIR" checkout --quiet "$ORIG_BRANCH"
}
trap cleanup EXIT

publish_branch() {
  local branch="$1" src="$2"

  echo "==> book@$branch <- ${src#"$CSWL_DIR"/}"
  cd "$BOOK_DIR"

  if [ -n "$(git status --porcelain)" ]; then
    echo "error: book@$(git branch --show-current) tem alterações não commitadas — resolva antes" >&2
    exit 1
  fi

  git fetch --quiet origin "$branch" 2>/dev/null || true

  if git show-ref --verify --quiet "refs/heads/$branch"; then
    git checkout --quiet "$branch"
    git merge --quiet --ff-only "origin/$branch" 2>/dev/null || true
  elif git show-ref --verify --quiet "refs/remotes/origin/$branch"; then
    git checkout --quiet -B "$branch" "origin/$branch"
  else
    git checkout --quiet --orphan "$branch"
    git reset --quiet --hard
  fi

  # Substitui a árvore inteira pelo conteúdo gerado, preservando só .git/.
  find . -mindepth 1 -maxdepth 1 ! -name .git -exec rm -rf {} +
  cp -R "$src"/. .

  git add -A
  if git diff --cached --quiet; then
    echo "    nada mudou"
  else
    git commit --quiet -m "Atualiza a partir de CSwL@$CSWL_SHA"
    git push --quiet origin "$branch"
    echo "    publicado"
  fi
}

publish_branch main "$LEAN_SRC"
publish_branch gh-pages "$HTML_SRC"
