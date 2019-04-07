import React, { Component } from "react";
import { WindowProgram, WindowAlert } from "packard-belle";
import cx from "classnames";
import Window from "../tools/Window";
import { buildMenu } from "../ExplorerWindow/ExplorerWindow";
import "./_styles.scss";

class IFrame extends Component {
  state = {
    displayAlert: this.props.data.displayAlert || true
  };

  confirm = () => this.setState({ displayAlert: false });

  render() {
    const { props, state } = this;

    const commonProps = {
      title: props.title,
      icon: props.icon,
      onClose: () => props.onClose(props.id)
    };

    if (state.displayAlert) {
      return (
        <WindowAlert
          {...commonProps}
          onOK={this.confirm}
          onCancel={commonProps.onClose}
          className="IframeWindow--alert"
        >
          {props.data.disclaimer ||
            `The Following is an iframe displaying, content belongs to the original creator at ${
              props.data.src
            }`}
        </WindowAlert>
      );
    }

    return (
      <Window
        {...props}
        resizable={!state.displayAlert}
        initialHeight={380}
        initialWidth={440}
      >
        {rnd => {
          return (
            <WindowProgram
              title={props.title}
              icon={props.icon}
              onClose={() => props.onClose(props.id)}
              onMinimize={() => props.onMinimize(props.id)}
              onRestore={rnd.restore}
              onMaximize={rnd.maximize}
              changingState={rnd.state.isDragging || rnd.state.isResizing}
              className={cx("IframeWindow", {
                "Window--active": props.isActive
              })}
              menuOptions={props.data.useMenu && buildMenu(props)}
              maximizeOnOpen={rnd.context.isMobile}
            >
              <iframe src={props.data.src} title={props.title} />
            </WindowProgram>
          );
        }}
      </Window>
    );
  }
}

export default IFrame;
