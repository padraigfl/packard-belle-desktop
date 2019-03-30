import React, { Component } from "react";
import { ProgramContext } from "../../contexts/programs";
import { WindowProgram, SelectBox, ButtonForm } from "packard-belle";
import Window from "../tools/Window";

import "./_task-manager.scss";
import { buildMenu } from "../ExplorerWindow/ExplorerWindow";

class TaskManager extends Component {
  static contextType = ProgramContext;
  state = {
    selected: null
  };

  onSelect = selected => this.setState({ selected });

  exit = () => {
    if (this.state.selected) {
      this.context.onClose(this.state.selected, true);
    }
  };

  moveToTop = () => {
    if (this.state.selected) {
      this.context.moveToTop(this.state.selected);
    }
  };

  render() {
    const { context, props } = this;
    return !context.taskManager ? (
      <Window
        {...props}
        resizable={false}
        initialX={200}
        initialY={150}
        initialWidth={240}
      >
        {rnd => (
          <WindowProgram
            title="Task Manager"
            className="TaskManager"
            onHelp={() => {}} // @todo
            onClose={context.toggleTaskManager}
            changingState={rnd.state.isDragging}
            resizable={false}
            menuOptions={buildMenu({
              ...props,
              onClose: context.toggleTaskManager
            })}
          >
            <SelectBox
              onClick={this.onSelect}
              options={context.openOrder.map(pid => {
                const prog = context.activePrograms.find(p => p.id === pid);
                return {
                  title: prog.title,
                  value: prog // key is based on value
                };
              })}
              selected={[this.state.selected]}
            />
            <div className="TaskManager__buttons">
              <ButtonForm onClick={this.exit}>End Task</ButtonForm>
              <ButtonForm onClick={this.moveToTop}>Switch To</ButtonForm>
              <ButtonForm isDisabled>New Task</ButtonForm>
            </div>
          </WindowProgram>
        )}
      </Window>
    ) : null;
  }
}

export default TaskManager;
