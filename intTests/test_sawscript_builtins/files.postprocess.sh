# If on Windows, we get an extra \r in the the include file.
# Suppress it.

# MSYS_NT is what the GH Windows runners produce. The
# other patterns are precautionary.
case "$(uname -s)" in
    MSYS_NT-*|[Ww]indows*|*[Cc]ygwin*|*[Ii]nterix*)
        sed '/\[104, 101, 108.*\]/s/13, //'
        ;;
    *)
        cat
        ;;
esac

