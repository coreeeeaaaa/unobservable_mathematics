import re
SELF = b'coreeeeaaaa@users.noreply.github.com'  # 본인 주소만 유지
def rewrite(msg: bytes) -> bytes:
    lines = msg.splitlines()
    keep = [ln for ln in lines if ln.lower().startswith(b'co-authored-by:') and SELF in ln]
    return b"chore: repository update\n" + (b"\n" + b"\n".join(keep) if keep else b"\n")