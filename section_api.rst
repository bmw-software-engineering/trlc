TRLC Iteration API by Section
=============================

This is description for the end-user facing TRLC Iteration API by Section

Function iter_record_objects_by_section() will yield
all the information about record objects, sections and file locations::

  def iter_record_objects_by_section(self):

You need to input trlc files with requirements which contain
sections or nested sections with record objects::

  # Iterates over each record object in the trlc files
  # and yields the file location of trlc files
  for record_object in self.iter_record_objects():
      file_name = record_object.location.file_name
      if location not in self.trlc_files:
          self.trlc_files.append(location)
          yield location

  # This code block checks section, if present
  # it will yield the section and level of section,
  # record object and level of record object
  if record_object.section:
      object_level = len(record_object.section) - 1
      for level, section in enumerate(record_object.section):
          if section not in self.section_names:
              self.section_names.append(section)
              yield section.name, level
      yield record_object, object_level

  # If section is not present
  # then it will yield the record object and level of record object
  else:
      object_level = 0
      yield record_object, object_level

