#!/usr/bin/env python3
"""Cache the pinned Lean reference manual with links usable through file://."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
from html import unescape
from html.parser import HTMLParser
import json
import posixpath
from pathlib import Path
import re
import subprocess
from urllib.parse import urljoin, urlsplit

ROOT = Path(__file__).resolve().parents[1]
BASE = "https://lean-lang.org/doc/reference/4.33.0/"
OUT = ROOT / ".deps/docs/lean-reference"
ATTR = re.compile(r"(\b(?:href|src)=)([\"'])(.*?)\2")


def local_path(url):
    suffix = urlsplit(url).path.removeprefix(urlsplit(BASE).path)
    return suffix + "index.html" if not suffix or suffix.endswith("/") else suffix


def fetch(url):
    path = OUT / local_path(url)
    path.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["curl", "-fsSL", "--retry", "2", "--max-time", "60", url,
                    "-o", str(path)], check=True)
    data = path.read_bytes()
    links = set()
    if path.suffix == ".html":
        text = data.decode()
        base = re.search(r'<base\s+href=["\']([^"\']+)', text)
        document_base = urljoin(url, unescape(base[1])) if base else url
        # Resolve original links against HTML's base, then remove it because the
        # mirrored links are relative to each local document.
        text = re.sub(r"<base\b[^>]*>", "", text)
        def replace(match):
            value = unescape(match[3])
            if value.startswith("#"):
                return match[0]
            absolute = urljoin(document_base, value)
            parts = urlsplit(absolute)
            clean = parts._replace(query="", fragment="").geturl()
            if not clean.startswith(BASE):
                if value.startswith("/"):
                    return match[1] + match[2] + absolute + match[2]
                return match[0]
            links.add(clean)
            relative = posixpath.relpath(local_path(clean), posixpath.dirname(local_path(url)) or ".")
            if parts.fragment:
                relative += "#" + parts.fragment
            return match[1] + match[2] + relative + match[2]
        class Rewriter(HTMLParser):
            def __init__(self):
                super().__init__(convert_charrefs=False)
                self.output = []

            def handle_starttag(self, tag, attrs):
                self.output.append(ATTR.sub(replace, self.get_starttag_text()))

            def handle_startendtag(self, tag, attrs):
                self.output.append(ATTR.sub(replace, self.get_starttag_text()))

            def handle_endtag(self, tag):
                self.output.append(f"</{tag}>")

            def handle_data(self, data):
                self.output.append(data)

            def handle_entityref(self, name):
                self.output.append(f"&{name};")

            def handle_charref(self, name):
                self.output.append(f"&#{name};")

            def handle_comment(self, data):
                self.output.append(f"<!--{data}-->")

            def handle_decl(self, decl):
                self.output.append(f"<!{decl}>")

        parser = Rewriter()
        parser.feed(text)
        path.write_text("".join(parser.output))
    elif path.suffix == ".css":
        for value in re.findall(r"url\(['\"]?([^)'\"]+)", data.decode()):
            clean = urljoin(url, value).split("#")[0]
            if clean.startswith(BASE):
                links.add(clean)
    return links, {"url": url, "path": str(path.relative_to(ROOT)),
                   "upstream_sha256": hashlib.sha256(data).hexdigest(),
                   "local_sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


if __name__ == "__main__":
    pending, seen, records = {BASE}, set(), []
    with ThreadPoolExecutor(max_workers=4) as pool:
        while pending:
            batch = sorted(pending - seen)
            if not batch:
                break
            seen.update(batch)
            if len(seen) > 1000:
                raise RuntimeError("unexpectedly large manual; refusing unbounded crawl")
            pending = set()
            for links, record in pool.map(fetch, batch):
                pending.update(links - seen)
                records.append(record)
            print(f"Cached {len(records)} manual pages/assets", flush=True)
    (ROOT / "dependencies/lean-manual.lock.json").write_text(
        json.dumps(sorted(records, key=lambda x: x["url"]), indent=2) + "\n")
