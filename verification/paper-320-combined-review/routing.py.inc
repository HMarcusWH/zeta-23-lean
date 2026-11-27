def documentation_epoch(repo):
    """Select the original validator from authenticated Git ancestry."""
    env = {**os.environ, 'GIT_NO_REPLACE_OBJECTS': '1', 'GIT_NO_LAZY_FETCH': '1'}
    def includes(anchor):
        command = ['git', '-C', str(repo), 'merge-base', '--is-ancestor', anchor, 'HEAD']
        result = subprocess.run(command, env=env, check=False, timeout=120)
        require(result.returncode in (0, 1), 'Cannot authenticate documentation ancestry')
        return result.returncode == 0
    registration = includes('f92691ef1d0cd8129e0df01cee747e5d70f939f6')
    paper = includes('b1e57c979ee75cf833c2c6587ff4049dee42a8f3')
    if registration and paper:
        return 'combined'
    if registration:
        return 'registration'
    return 'paper' if paper else 'historical'


def validate_descendant(repo, *, require_clean=False):
    epoch = documentation_epoch(repo)
    require(epoch != 'combined', 'Combined documentation requires independently reviewed source admission')
    if epoch == 'registration':
        from ..opica_dispatch_registration.gate import validate_descendant as original
    elif epoch == 'paper':
        from ..documentation_2026_11_26.source_scope import validate_descendant as original
    else:
        from ..documentation_2026_11_21.source_scope import validate_descendant as original
    return original(repo, require_clean=require_clean)
