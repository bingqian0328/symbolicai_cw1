from z3 import *
from pathlib import Path
from timeit import default_timer as timer
import re

class Instance:
    def __init__(self):
        self.number_of_students = 0
        self.number_of_exams = 0
        self.number_of_slots = 0
        self.number_of_rooms = 0
        self.room_capacities = []
        self.exams_to_students = []
        self.student_exam_capacity = []

def read_file(filename):
    def read_attribute(name):
        line = f.readline()
        match = re.match(f'{name}:\\s*(\\d+)$', line)
        if match:
            return int(match.group(1))
        else:
            raise Exception(f"Could not parse line {line}; expected the {name} attribute")

    instance = Instance()
    with open(filename) as f:
        instance.number_of_students = read_attribute("Number of students")
        instance.number_of_exams = read_attribute("Number of exams")
        instance.number_of_slots = read_attribute("Number of slots")
        instance.number_of_rooms = read_attribute("Number of rooms")

        for r in range(instance.number_of_rooms):
            instance.room_capacities.append(read_attribute(f"Room {r} capacity"))

        while True:
            l = f.readline()
            if l == "":
                break
            m = re.match('^\\s*(\\d+)\\s+(\\d+)\\s*$', l)
            if m:
                instance.exams_to_students.append((int(m.group(1)), int(m.group(2))))
            else:
                raise Exception(f'Failed to parse this line: {l}')

    instance.student_exam_capacity = [0] * instance.number_of_exams
    for exam, student in instance.exams_to_students:
        instance.student_exam_capacity[exam] += 1
    return instance

def solve(instance):
    start_solve = timer()  # Timer for solving the instance
    s = Solver()

    # Variable Declarations
    exam = Int('exam')
    room = Int('room')
    timeslot = Int('timeslot')
    next_exam = Int('next_exam')
    next_timeslot = Int('next_timeslot')
    student = Int('student')

    # Range Functions for Constraints
    Student_Range = Function('Student_Range', IntSort(), BoolSort())
    Exam_Range = Function('Exam_Range', IntSort(), BoolSort())
    Room_Range = Function('Room_Range', IntSort(), BoolSort())
    TimeSlot_Range = Function('TimeSlot_Range', IntSort(), BoolSort())

    # Range Constraints
    s.add(ForAll([student], Student_Range(student) == And(student >= 0, student < instance.number_of_students)))
    s.add(ForAll([exam], Exam_Range(exam) == And(exam >= 0, exam < instance.number_of_exams)))
    s.add(ForAll([timeslot], TimeSlot_Range(timeslot) == And(timeslot >= 0, timeslot < instance.number_of_slots)))
    s.add(ForAll([room], Room_Range(room) == And(room >= 0, room < instance.number_of_rooms)))

    # Functions for Exam Room, Time, and Students
    ExamRoom = Function('ExamRoom', IntSort(), IntSort())      # Maps each exam to a room
    ExamTime = Function('ExamTime', IntSort(), IntSort())      # Maps each exam to a timeslot
    ExamStudent = Function('ExamStudent', IntSort(), IntSort(), BoolSort())  # Indicates if a student is taking an exam

    # Add Students Taking Exams based on Input Data
    for exam_id, student_id in instance.exams_to_students:
        s.add(ExamStudent(exam_id, student_id))


    # Constraint 1 and 2: Room and Time Assignments for Exams
    s.add(
    ForAll([exam],
           Implies(
               Exam_Range(exam),
               Exists([room, timeslot],
                      And(
                          Room_Range(room),
                          TimeSlot_Range(timeslot),
                          ExamTime(exam) == timeslot,
                          ExamRoom(exam) == room,
                          # Ensure that no two exams occupy the same room and time slot
                          Not(Exists([next_exam],
                                     And(
                                         Exam_Range(next_exam),
                                         And(
                                             ExamRoom(next_exam) == room,
                                             ExamTime(next_exam) == timeslot,
                                             exam != next_exam
                                         )
                                     )
                          ))
                      )
               )
           )
        )
    )

    # Constraint 3: Room Capacity
    for ex in range(instance.number_of_exams):
        for rm in range(instance.number_of_rooms):
            s.add(Implies(ExamRoom(ex) == rm, instance.student_exam_capacity[ex] <= instance.room_capacities[rm]))

    # Constraint 4: Non-overlapping Exams for Students
    s.add(
        ForAll([student, exam, next_exam, timeslot, next_timeslot],
               Implies(
                   And(
                       Student_Range(student),
                       Exam_Range(exam),
                       Exam_Range(next_exam),
                       TimeSlot_Range(timeslot),
                       TimeSlot_Range(next_timeslot),
                       exam != next_exam
                   ),
                   Implies(
                       And(
                           ExamTime(exam) == timeslot,
                           ExamTime(next_exam) == next_timeslot,
                           ExamStudent(exam, student),
                           ExamStudent(next_exam, student)
                       ),
                       And(timeslot + 1 != next_timeslot, timeslot - 1 != next_timeslot, timeslot != next_timeslot)  # Ensure no adjacent time slots for same student
                   )
               )
        )
    )

    # Check if the constraints are satisfiable
    if s.check() == sat:
        students_with_many_exams = []
        print('Satisfied')
        m = s.model()  # Only get the model when satisfiable
        print("――――――――――――Exam Timetable――――――――――――--")
        for ex in range(instance.number_of_exams):
            room = m.eval(ExamRoom(ex))
            slot = m.eval(ExamTime(ex))
            students_count = instance.student_exam_capacity[ex]
            print(f"Exam: {ex} | Room: {room} | Slot: {slot} | Students: {students_count}")
        print("――――――――――――――――――――――――----------------")

        # Print Individual Timetable for Each Student
        print("―――――――――――Individual Timetables (Exam, Slot, Room)―――――――――――")
        for student_id in range(instance.number_of_students):
             
            exams_for_student = [
                (exam, m.eval(ExamTime(exam)), m.eval(ExamRoom(exam)))
                for exam, stud in instance.exams_to_students
                if stud == student_id
            ]

            if exams_for_student:
                exams_formatted = " | ".join(f"({ex}, {slot}, {room})" for ex, slot, room in exams_for_student)
                print(f"Student {student_id}: {exams_formatted}")

                # Track students with more than 3 exams
                if len(exams_for_student) > 3:
                    students_with_many_exams.append(student_id)
            else:
                print(f"Student {student_id}: Student is not scheduled for any exam, please check with the student office.")

        # Print warning if any student has more than 3 exams
        if students_with_many_exams:
            students_list = ", ".join(map(str, students_with_many_exams))
            print(f"Warning: Student(s) {students_list} are scheduled for more than 3 exams!")

        print("――――――――――――――――――――――――--------------------------------------")
    else:
        print('Unsatisfied')

    end_solve = timer()  # Timer ends after solving the instance
    print(f"Time taken to solve the instance: {int((end_solve - start_solve) * 1000)} ms\n")


if __name__ == "__main__":
    start = timer()
    directory = "./test instances"
    # Loop through all txt files in the specified directory
    for filename in Path(directory).glob("*.txt"):
        instance = read_file(filename)
        print(f"{filename}: ", end="")
        solve(instance)
    end = timer()
    print('Elapsed time:', int((end - start) * 1000), 'milliseconds')


