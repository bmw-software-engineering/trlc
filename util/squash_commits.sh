#!/bin/bash
 
set -e  # Exit immediately if any command exits with a non-zero status
 
# Function: check if the environment is clean
# checks for unstagged (diff --quiet) or stagged but uncommited changes (git diff --cached --quiet)
check_clean_worktree() {
    if ! git diff --quiet || ! git diff --cached --quiet; then
        echo "Error: Uncommitted changes detected. Please commit or stash changes first."
        exit 1
    fi
}
 
fetch_and_rebase() {
    CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
    git fetch origin
    echo "Checking if the branch is up to date with 'origin/$CURRENT_BRANCH'..."
    if ! git diff --quiet "$CURRENT_BRANCH" "origin/$CURRENT_BRANCH"; then
        echo "Branch is out of date. Rebasing onto 'origin/$CURRENT_BRANCH'..."
        git rebase "origin/$CURRENT_BRANCH" || handle_rebase_conflicts
    fi
}
 
handle_rebase_conflicts() {
    while ! git rebase --continue 2>/dev/null; do
        echo "Resolve conflicts, stage the changes, and reattempting 'git rebase --continue'..."
        read -p "Press ENTER after resolving conflicts and staging changes."
    done
}
 
# Squash commits interactively
interactive_squash() {
    echo "Starting interactive rebase to squash commits into one..."
    git rebase -i origin/main || handle_rebase_conflicts
}

# Function to force push changes after confirmation
force_push_with_confirmation() {
    read -p "Do you want to force push the changes to the remote branch? (yes/no): " RESPONSE
    case "$RESPONSE" in
        [Yy][Ee][Ss]|[Yy])
            CURRENT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
            echo "Force pushing changes to 'origin/$CURRENT_BRANCH'..."
            git push --force-with-lease
            echo "Changes successfully pushed to remote."
            ;;
        *)
            echo "Force push canceled. Your changes are local only."
            ;;
    esac
}
 
# Main script execution
main() {
    check_clean_worktree
    fetch_and_rebase
    interactive_squash
    echo "Rebase and squash completed successfully."
    force_push_with_confirmation
}
 
# Entry point
main