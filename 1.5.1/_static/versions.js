// Adapted from:
// https://github.com/brechtm/rinohtype/commit/1270802c4959eb4742c51d3307222930ac73a80c
$(document).ready(function () {
    $.getJSON('/saw-script/versions.json', function (data) {
        if (data.length > 0) {
            var versions = [];
            $.each(data, function (index, value) {
                versions.push(value);
            });
            var dl = document.getElementById('docs-versions');
            $.each(versions, function (i, v) {
                var version = versions[i];
                dl.innerHTML = dl.innerHTML +
                    '<dd><a href="/saw-script/' + version + '">' + version + '</a></dd>'
            });

        }
    });
});
