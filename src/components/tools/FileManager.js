import React from "react";
import { Rnd } from "react-rnd";
import { ProgramContext } from "../../contexts";
import { WindowAction } from "packard-belle";

const initialPostiions = () => {
  if (!window || window.innerWidth < 400) {
    return { x: 0, y: 0 };
  }
  const screen = document.getElementsByClassName("w98")[0];
  return {
    x: (screen.clientWidth - 350) / 2,
    y: (screen.clientHeight - 200) / 2
  };
};

class FileManager extends React.Component {
  static contextType = ProgramContext;
  state = {
    ...initialPostiions(),
    name: this.props.name || ""
  };

  updateLocation = (a, b) =>
    this.setState({ x: b.x, y: b.y, isDragging: false });
  toggleDrag = val => () => this.setState({ isDragging: val });
  onChangeName = val => {
    this.setState({ name: val });
  };

  save = () => {
    this.context.save(
      this.props.instance,
      this.props.data,
      this.state.name,
      this.props.location
    );
    this.props.onAction();
  };

  open = () => {
    const prog = this.context[this.props.location || "desktop"].find(
      p => p.title === this.state.name
    );
    if (prog) {
      this.context.onOpen(prog);
      this.props.onAction();
    }
  };

  getFolder = () =>
    this.context[this.props.location]
      .filter(v => v.component === this.props.instance.component)
      .map(v => ({ ...v, value: v.title }));

  render() {
    const { props } = this;
    return (
      <Rnd
        position={{ x: this.state.x, y: this.state.y }}
        dragHandleClassName="Window__title"
        onDragStart={this.toggleDrag(true)}
        onDragStop={!this.state.maximized && this.updateLocation}
        bounds=".w98"
        enableResizing={false}
      >
        <WindowAction
          type={props.type}
          action={props.actionName}
          onCancel={props.onCancel}
          onAction={this[props.actionName]}
          onChangeName={this.onChangeName}
          content={props.action === "open" ? this.getFolder() : props.content}
          name={this.state.name}
          className="Window--active"
        />
      </Rnd>
    );
  }
}

FileManager.defaultProps = {
  minWidth: 200,
  minHeight: 200,
  initialWidth: 250,
  initialHeight: 250,
  // maxHeight: 448,
  // maxWidth: 635,
  resizable: true,

  scale: 1,
  title: "Needs default"
};

export default FileManager;
