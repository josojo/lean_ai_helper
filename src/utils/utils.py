def remove_last_slash(s: str) -> str:
    return s[:-1] if s.endswith("/") else s
