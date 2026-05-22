from pathlib import Path
import tarfile

from docutils import nodes

from sphinx.addnodes import download_reference
from sphinx.application import Sphinx

from sphinx.util.docutils import ReferenceRole
from sphinx.util.typing import ExtensionMetadata


""" Read the documentation timestamp from epoch.mk
"""
def read_docs_epoch(path):
    with open(path, 'rt') as ef:
        for line in ef.readlines():
            if line.startswith("SOURCE_DATE_EPOCH="):
                epoch = int(line[18:].strip())
                return epoch
    raise(RuntimeError("Did not find SOURCE_DATE_EPOCH= in epoch.mk"))

class DownloadDirRole(ReferenceRole):
    """Role providing directory downloads.

    Injects a suitable download reference after making a tar.gz archive of the
    directory.
    """

    def run(self) -> tuple[list[nodes.Node], list[nodes.system_message]]:
        epochfile = Path(self.env.srcdir) / "scripts" / "epoch.mk"
        timestamp = read_docs_epoch(epochfile)

        def adjustinfo(info):
            info.mtime = timestamp
            return info

        dir_to_download = Path(self.env.relfn2path(self.target)[1])

        if not dir_to_download.is_dir():
            msg = self.inliner.reporter.error(
                f"download-dir expects a source directory path, but {self.target} does not resolve to a directory -- Skipping."
            )
            return [], [msg]

        out_tar = dir_to_download.with_suffix(".tar.gz")
        self.env.note_dependency(str(out_tar))

        with tarfile.open(out_tar, "w:gz") as ot:
            for child in dir_to_download.iterdir():
                ot.add(child, filter=adjustinfo)

        download_node = download_reference(
            reftarget=f"/{out_tar.relative_to(self.env.srcdir)}",
        )
        download_node.append(
            nodes.literal(
                text=self.title if self.has_explicit_title else out_tar.name,
                classes=["download"],
            )
        )

        return [download_node], []


def setup(app: Sphinx) -> ExtensionMetadata:
    app.add_role("download-dir", DownloadDirRole())

    return {
        "version": "0.0.1",
        "parallel_read_safe": True,
    }
