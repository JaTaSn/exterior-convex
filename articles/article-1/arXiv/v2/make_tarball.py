#!/usr/bin/env python3
"""Build arXiv-v2.tar.gz, the upload for the arXiv replacement of Part I (2609.23605v2).

    python3 make_tarball.py

Needs only Python 3 (standard library): no LaTeX, no Emacs.  Run it on any machine with a clone of
this repository.  The archive holds exactly the tracked upload files of this directory:

    exterior-convex_article1_latest.tex
    img/*            (the nine figures the .tex includes)

and nothing else: no README, no metadata, no preview PDF, no Org source, no anc/.  The script
checks that every figure the .tex includes is present and that no figure is left over, and prints
the SHA-256 of the .tex so that two machines can compare what they are about to upload.

Entries are sorted, and owner, group and modification time are fixed, so the same files give the
same uncompressed archive everywhere; its SHA-256 is printed, and that is the number to compare
between machines.  The .tar.gz itself is NOT byte-identical across machines: different versions
of the compression library produce different gzip output from the same input (seen 2026-11-24,
jts-mini 477832 bytes against jts-pc 473040, with identical contents).
"""
import gzip, hashlib, io, pathlib, re, sys, tarfile

HERE = pathlib.Path(__file__).resolve().parent
TEX = HERE / "exterior-convex_article1_latest.tex"
OUT = HERE / "arXiv-v2.tar.gz"


def main():
    if not TEX.exists():
        sys.exit(f"missing {TEX.name}")
    tex = TEX.read_text(encoding="utf-8")
    wanted = sorted(set(re.findall(r"\\includegraphics(?:\[[^]]*\])?\{([^}]*)\}", tex)))
    missing = [w for w in wanted if not (HERE / w).is_file()]
    if missing:
        sys.exit(f"the .tex includes figures that are not here: {missing}")
    present = sorted(p.relative_to(HERE).as_posix() for p in (HERE / "img").iterdir() if p.is_file())
    extra = [p for p in present if p not in wanted]
    if extra:
        sys.exit(f"img/ holds files the .tex does not include: {extra}")
    if "\\printbibliography" in tex or "{biblatex}" in tex:
        sys.exit("the .tex still uses biblatex; this is not the arXiv form")

    members = [TEX.name] + wanted
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w", format=tarfile.PAX_FORMAT) as tf:
        for name in members:
            data = (HERE / name).read_bytes()
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = len(data), 0o644, 0
            info.uid = info.gid = 0
            info.uname = info.gname = ""
            tf.addfile(info, io.BytesIO(data))
    with open(OUT, "wb") as fh, gzip.GzipFile(fileobj=fh, mode="wb", mtime=0, filename="") as gz:
        gz.write(buf.getvalue())

    print(f"wrote {OUT.name}: {OUT.stat().st_size} bytes, {len(members)} files")
    for name in members:
        print("  ", name)
    print("SHA-256 of the .tex:  ", hashlib.sha256(TEX.read_bytes()).hexdigest())
    print("SHA-256 of the contents (uncompressed archive; compare THIS between machines):")
    print("  ", hashlib.sha256(buf.getvalue()).hexdigest())
    back = gzip.decompress(OUT.read_bytes())
    if back != buf.getvalue():
        sys.exit("the written .tar.gz does not decompress to the archive that was built")
    print("the .tar.gz decompresses to exactly that archive; its own bytes may differ between machines")


if __name__ == "__main__":
    main()
