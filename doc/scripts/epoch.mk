# This is the date used for the documentation build.
# (It does not, and should not, leak out into the rest of SAW.)
# Among other things it appears on the cover page of the manual.
#
# Bump this date to the current date if you make anything more than
# completely trivial changes to the manual and tutorial content.
# (But don't let it move backwards.)
#
# Update procedure here is:
#    - pick a date/time
#    - update the human-readable date in the comments
#    - then run whichever of the commands in the comment matches your system
#    - and also update the SOURCE_DATE_EPOCH value
#
# Notes on the date:
#    - we used April 1 as an arbitrary choice when we first deployed
#      this in 1.2.0.99
#    - 1.3 was released March 21, used April 2 so as not to go backwards
#    - 1.3.0.99 will use April 3
#    - if it needs to be changed before 1.4, use successive days (until
#      we're past April 3, then use the current day)
#    - for 1.4 and beyond, use the release date for the release and the
#      day after for the following devel version
#    - the devel version can then be bumped to the current day if needed
#

# BSD/Linux: date +%s -d "09/17/2025 00:00:00 GMT"
# OSX: date -j -f "%m/%d/%Y %H:%M:%S %Z" "9/17/2025 00:00:00 GMT" +%s
SOURCE_DATE_EPOCH=1758067200
