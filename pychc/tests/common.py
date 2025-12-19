import functools


def reset_pysmt_env(test_func):
    @functools.wraps(test_func)
    def _wrapper(*args, **kwargs):
        from pychc.environment import reset_env

        reset_env()
        return test_func(*args, **kwargs)

    return _wrapper
