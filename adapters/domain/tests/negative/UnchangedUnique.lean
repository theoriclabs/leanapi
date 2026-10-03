import NativeCommandsChecks

-- Changing only name must not acquire an unrelated email business alternative.
def impossible : NativeCommandsChecks.rename.Error := .emailTaken
