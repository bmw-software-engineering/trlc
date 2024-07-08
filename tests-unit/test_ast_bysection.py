import unittest
from unittest.mock import MagicMock
from trlc.ast import Symbol_Table

class TestIterRecordObjectsBySection(unittest.TestCase):
    def setUp(self):
        self.mock_self = MagicMock(spec=Symbol_Table)
        self.mock_self.trlc_files = []
        self.mock_self.section_names = []
        self.mock_self.iter_record_objects.return_value = [
            MagicMock(location=MagicMock(file_name='file1.txt'), section=['Section1', 'Subsection1']),
            MagicMock(location=MagicMock(file_name='file2.txt'), section=['Section2']),
            MagicMock(location=MagicMock(file_name='file1.txt'), section=None)
        ]

    def test_iter_record_objects_by_section(self):        
        sys = Symbol_Table()
        result = list(sys.iter_record_objects_by_section())
        # result = list(self.mock_self.iter_record_objects_by_section())

        self.assertEqual(result, [
            'file1.txt',
            'file2.txt',
            ('Section1', 0),
            ('Subsection1', 1),
            ('Section2', 0),
            (self.mock_self.iter_record_objects.return_value[0], 1),
            (self.mock_self.iter_record_objects.return_value[1], 0),
            (self.mock_self.iter_record_objects.return_value[2], 0),
        ])

        self.assertEqual(self.mock_self.trlc_files, ['file1.txt', 'file2.txt'])
        self.assertEqual(self.mock_self.section_names, ['Section1', 'Subsection1', 'Section2'])

if __name__ == '__main__':
    unittest.main()
    